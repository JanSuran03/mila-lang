(ns mila-lang.parser.semantical-analyzer
  (:require [clojure.pprint :as pp]
            [mila-lang.parser.core :as parser])
  (:import (clojure.lang ExceptionInfo)
           (java.io File)
           (mila_lang.parser.proto CArg
                                   CArithmAdd
                                   CArithmDiv
                                   CArithmMod
                                   CArithmMul
                                   CArithmSub
                                   CArithmUnNeg
                                   CArrayType
                                   CAssignment
                                   CBeginEndBlock
                                   CCall
                                   CCmpEq
                                   CCmpGt
                                   CCmpGe
                                   CCmpLt
                                   CCmpLe
                                   CCmpNe
                                   CConst
                                   CDowntoFor
                                   CExit
                                   CFunction
                                   CIfElse
                                   CIndexAssignment
                                   CIndexOp
                                   CInteger
                                   CLogAnd
                                   CLogOr
                                   CProcedure
                                   CProgram
                                   CString
                                   CSymbol
                                   CToFor
                                   CVarDecl
                                   CWhile)))

(defrecord AnalyzeContext [constants externs forwards functions idents return-type vars])

(defprotocol IAnalyzable
  (-analyze [this table-of-symbols]
    "Checks, whether the program symbols and the semantics of the operations
    are in compliance with their associated (return) types."))

(def ^:dynamic *current-function* nil)
(def ^:dynamic *current-return-type* nil)
(def ^:dynamic *current-fn-args* {})

(defn ->>analyze [context blocks]
  (reduce #(-analyze %2 %1) context blocks))

(defn rec->type [x]
  (condp instance? x
    CInteger :token/integer-TYPE
    CString :string-TYPE
    CArrayType (rec->type (.-type ^CArrayType x))))

(defn- +return-type [ctx type]
  (assoc ctx :return-type type))

(defn- +ident [ctx ident]
  (update ctx :idents conj ident))

(defn- +const [ctx ident type]
  (-> ctx (update :constants assoc ident type)
      (+ident ident)))

(defn- +var [ctx ident type]
  (-> ctx (update :vars assoc ident type)
      (+ident ident)))

(defn- +function [ctx ident arg-types ret-type]
  (-> ctx (update :functions assoc (into [ident] arg-types) ret-type)
      (+ident ident)))

(defn- +forward-function [ctx ident arg-types ret-type]
  (-> ctx (update :forwards assoc ident {:arg-types arg-types :ret-type ret-type})
      (+ident ident)))

(defn- +procedure [ctx ident arg-types]
  (+function ctx ident arg-types :void-TYPE))

(defn- +forward-procedure [ctx ident arg-types]
  (-> ctx (update :forwards assoc ident {:arg-types arg-types :ret-type :void-TYPE})
      (+ident ident)))

(extend-type CProgram
  IAnalyzable
  (-analyze [this context]
    (->>analyze context (.-program-blocks this))))

(extend-type CConst
  IAnalyzable
  (-analyze [{:keys [lhs rhs]} context]
    (if ((.-constants ^AnalyzeContext context) lhs)
      (throw (ex-info "Error: redefinition of constant" {:constant-name lhs}))
      (+const context lhs (rec->type rhs)))))

(extend-type CVarDecl
  IAnalyzable
  (-analyze [{:keys [vars type] :as this} context]
    (reduce (fn [context var-name]
              (if ((.-idents ^AnalyzeContext context) var-name)
                (throw (ex-info "Error: redefinition of var" {:var-name var-name}))
                (+var context var-name type)))
            context
            vars)))

(extend-type CAssignment
  IAnalyzable
  (-analyze [{:keys [lhs rhs]} {:keys [vars] :as context}]
    (cond (= lhs *current-function*)
          (let [{:keys [return-type]} (-analyze rhs context)]
            (if (identical? return-type *current-return-type*)
              context
              (throw (ex-info "Cannot return from function - return types micmatch" {:function lhs
                                                                                     :expected *current-return-type*
                                                                                     :actual   return-type}))))

          (vars lhs)
          (let [{:keys [return-type] :as context} (-analyze rhs context)]
            (if (= return-type (vars lhs))
              context
              (ex-info "Cannot assign to var: incompatible type" {:var-name lhs
                                                                  :expected (vars lhs)
                                                                  :actual   return-type})))

          (*current-fn-args* lhs)
          (let [{:keys [return-type] :as context} (-analyze rhs context)]
            (if (= return-type (*current-fn-args* lhs))
              context
              (ex-info "Cannot assign to var: incompatible type" {:var-name lhs
                                                                  :expected (*current-fn-args* lhs)
                                                                  :actual   return-type})))

          :else
          (throw (ex-info "Cannot resolve assignment variable" {:name lhs})))))

(extend-type CIndexAssignment
  IAnalyzable
  (-analyze [{:keys [arr index-expr rhs]} context]
    (if-let [arr-type (:type ((.-vars ^AnalyzeContext context) arr))]
      (let [index-expr-type (:return-type (-analyze index-expr context))]
        (if (identical? index-expr-type :token/integer-TYPE)
          (let [rhs-type (:return-type (-analyze rhs context))]
            (if (identical? rhs-type arr-type)
              context
              (throw (ex-info "Cannot assign to an array of a different type" {:array-name arr
                                                                               :array-type arr-type
                                                                               :rhs-type   rhs-type}))))
          (throw (ex-info "Cannot index array wit ha non-integral type" {:array-name      arr
                                                                         :index-expr-type index-expr-type}))))
      (throw (ex-info "Cannot resolve array in context" {:array-name arr})))))

(extend-type CBeginEndBlock
  IAnalyzable
  (-analyze [this context]
    (->>analyze context (.-blocks this))))

(extend-type CCall
  IAnalyzable
  (-analyze [{:keys [target args]} {:keys [functions externs] :as context}]
    (let [arg-types (mapv #(.-return-type ^AnalyzeContext (-analyze % context)) args)
          full-fn-signature (into [target] arg-types)]
      (if-let [return-type (or (externs full-fn-signature) (functions full-fn-signature))]
        (+return-type context return-type)
        (throw (ex-info "Could not find function declaration" {:name  target
                                                               :types arg-types}))))))

(extend-type CString
  IAnalyzable
  (-analyze [this context]
    (+return-type context :string-TYPE)))

(extend-type CInteger
  IAnalyzable
  (-analyze [this context]
    (+return-type context :token/integer-TYPE)))

(defn analyze-fn-arglist [context fn-name arglist]
  (reduce (fn [[ctx args arg-types] {arg-name :name arg-type :type}]
            (when (or (= arg-name fn-name) ((.-idents ^AnalyzeContext ctx) arg-name))
              (throw (ex-info "Argument cannot shadow symbol that is already declared in the scope." {:name     arg-name
                                                                                                      :function fn-name})))
            (when (args arg-name)
              (throw (ex-info "Argument name duplicate." {:name     arg-name
                                                          :function fn-name})))
            [(+const ctx arg-name arg-type) (assoc args arg-name arg-type) (conj arg-types arg-type)])
          [context {} []]
          arglist))

(extend-type CFunction
  IAnalyzable
  (-analyze [{:keys [name arglist return-type locals body forward]} context]
    (let [declared-sig ((.-forwards ^AnalyzeContext context) name)]
      (cond declared-sig
            (if forward
              (throw (ex-info "Cannot forward-declare a function twice" {:name name}))
              (let [[fn-body-ctx args arg-types] (analyze-fn-arglist context name arglist)
                    _ (when (not= {:arg-types arg-types :ret-type return-type}
                                  ((.-forwards ^AnalyzeContext context) name))
                        (throw (ex-info "Cannot define a declared function, signature mismatch" {:declared (assoc declared-sig
                                                                                                             :name name)
                                                                                                 :defined  {:arg-types arg-types
                                                                                                            :ret-type  return-type
                                                                                                            :name      name}})))
                    forward->defined-ctx (-> context (update :forwards dissoc name)
                                             (+function name arg-types return-type))
                    forward->defined-ctx (->>analyze forward->defined-ctx locals)
                    forward->defined-ctx (+function forward->defined-ctx name arg-types return-type)]
                (binding [*current-function* name
                          *current-return-type* return-type
                          *current-fn-args* args]
                  (-analyze body fn-body-ctx))
                forward->defined-ctx))

            ((.-idents ^AnalyzeContext context) name)
            (throw (ex-info "Identifier cannot be redefined" {:ident name}))

            :else
            (let [[fn-body-ctx args arg-types] (analyze-fn-arglist context name arglist)
                  ret-decl-context (+function context name arg-types return-type)]
              (if forward
                (+forward-function ret-decl-context name arg-types return-type)
                (let [fn-body-ctx (->>analyze fn-body-ctx locals)
                      fn-body-ctx (+function fn-body-ctx name arg-types return-type)]
                  (binding [*current-function* name
                            *current-return-type* return-type
                            *current-fn-args* args]
                    (-analyze body fn-body-ctx))
                  ret-decl-context)))))))

(extend-type CProcedure                                     ; TODO: IMPLEMENT FORWARD
  IAnalyzable
  (-analyze [{:keys [name arglist locals body forward]} context]
    (when ((.-idents ^AnalyzeContext context) name)
      (throw (ex-info "Identifier cannot be redefined" {:ident name})))
    (let [[proc-body-ctx args arg-types] (analyze-fn-arglist context name arglist)
          ret-decl-context (+procedure context name arg-types)]
      (if forward
        (+forward-procedure ret-decl-context name arg-types)
        (let [proc-body-ctx (->>analyze proc-body-ctx locals)
              proc-body-ctx (+procedure proc-body-ctx name arg-types)]
          (binding [*current-function* name
                    *current-return-type* :void-TYPE
                    *current-fn-args* args]
            (-analyze body proc-body-ctx))
          ret-decl-context)))))

(defmacro extend-arithm-op [rec op-sym]
  `(extend-type ~rec
     IAnalyzable
     (-analyze [{:keys [~'lhs ~'rhs]} context#]
               (let [{ret-type-1# :return-type} (-analyze ~'lhs context#)
                     {ret-type-2# :return-type} (-analyze ~'rhs context#)]
                 (if (= ret-type-1# ret-type-2# :token/integer-TYPE)
                   (+return-type context# :token/integer-TYPE)
                   (throw (ex-info ~(str "Cannot call operator '" op-sym "' on two non-integer types") {:lhs ret-type-1#
                                                                                                        :rhs ret-type-2#})))))))

(extend-arithm-op CArithmAdd "+")
(extend-arithm-op CArithmDiv "/")
(extend-arithm-op CArithmMod "%")
(extend-arithm-op CArithmMul "*")
(extend-arithm-op CArithmSub "-")
(extend-arithm-op CCmpEq "=")
(extend-arithm-op CCmpGt ">")
(extend-arithm-op CCmpGe ">=")
(extend-arithm-op CCmpLt "<")
(extend-arithm-op CCmpLe "<=")
(extend-arithm-op CCmpNe "<>")
(extend-arithm-op CLogAnd "&&")
(extend-arithm-op CLogOr "||")

(extend-type CSymbol
  IAnalyzable
  (-analyze [{:keys [value]} ^AnalyzeContext context]
    (if-let [rt-fn-arg (*current-fn-args* value)]
      (+return-type context rt-fn-arg)
      (if-let [rt-var (or (when (= *current-function* value)
                            *current-return-type*)
                          ((.-vars context) value))]
        (+return-type context rt-var)
        (if-let [rt-const ((.-constants context) value)]
          (+return-type context rt-const)
          (if ((.-idents context) value)
            (throw (ex-info "Symbol resolved, but not directly accessible" {:symbol value}))
            (throw (ex-info "Symbol cannot be resolved" {:symbol value}))))))))

(extend-type CIndexOp
  IAnalyzable
  (-analyze [{:keys [arr-name index-expr]} {:keys [vars] :as context}]
    (if-let [^CArrayType full-arr-type (vars arr-name)]
      (if (instance? CArrayType full-arr-type)
        (let [{:keys [return-type]} (-analyze index-expr context)]
          (if (identical? return-type :token/integer-TYPE)
            (+return-type context ^CArrayType (.-type full-arr-type))
            (throw (ex-info "Cannot index an array an expression that is not integral" {:arr-name        arr-name
                                                                                        :index-expr-type return-type}))))
        (throw (ex-info "Cannot index a variable that is not an array" {:var arr-name})))
      (if (.-idents ^AnalyzeContext context)
        (throw (ex-info "Identifier is not an array:" {:identifier arr-name}))
        (throw (ex-info "Array cannot be resolved" {:array-name arr-name}))))))

(extend-type CExit
  IAnalyzable
  (-analyze [_this context]
    (if *current-return-type*
      context
      (throw (ex-info "Cannot call 'exit' if not inside a function or procedure" {:current-function *current-function*})))))

(extend-type CWhile
  IAnalyzable
  (-analyze [{:keys [cond body]} context]
    (let [cond-ret-type (:return-type (-analyze cond context))]
      (if (= cond-ret-type :token/integer-TYPE)
        (-analyze body context)
        (throw (ex-info "While loop condition has to return an integer" {:cond-ret-type cond-ret-type}))))))

(extend-type CIfElse
  IAnalyzable
  (-analyze [{:keys [cond then else]} context]
    (let [cond-return-type (:return-type (-analyze cond context))]
      (if (identical? cond-return-type :token/integer-TYPE)
        (do (-analyze then context)
            (when else
              (-analyze else context))
            context)
        (throw (ex-info "If-else condition must return an integer" {:cond-return-type cond-return-type}))))))

(defn analyze-to-downto [{:keys [iter-var iter-var-init iter-var-end body]} ^AnalyzeContext context]
  (let [iter-var-type ((.-vars context) iter-var)]
    (cond (nil? iter-var-type)
          (if ((.-idents context) iter-var)
            (throw (ex-info "Iteration variable is not a var" {:var-name iter-var}))
            (throw (ex-info "Iteration variable not declared" {:var-name iter-var})))

          (not (identical? :token/integer-TYPE iter-var-type))
          (throw (ex-info "for-to variable must be an integer" {:var-name    iter-var
                                                                :actual-type iter-var-type}))

          :else
          (let [iter-init-type (:return-type (-analyze iter-var-init context))]
            (if (identical? iter-init-type :token/integer-TYPE)
              (let [iter-end-type (:return-type (-analyze iter-var-end context))]
                (if (identical? iter-end-type :token/integer-TYPE)
                  (do (-analyze body context)
                      context)
                  (ex-info "for-to variable end must be an integer" {:var-name    iter-var
                                                                     :actual-type iter-end-type})))
              (ex-info "for-to variable init must be an integer" {:var-name    iter-var
                                                                  :actual-type iter-init-type}))))))

(extend-type CToFor
  IAnalyzable
  (-analyze [this context]
    (analyze-to-downto this context)))

(extend-type CDowntoFor
  IAnalyzable
  (-analyze [this context]
    (analyze-to-downto this context)))

(extend-type CArithmUnNeg
  IAnalyzable
  (-analyze [{:keys [val]} ^AnalyzeContext context]
    (let [{:keys [return-type]} (-analyze val context)]
      (if (= return-type :token/integer-TYPE)
        context
        (throw (ex-info "Cannot negate an expression that is not integral" {:return-type return-type}))))))

(defn analyze [expr]
  (-analyze expr (map->AnalyzeContext {:constants   {}
                                       :externs     {["dec" :token/integer-TYPE]     "dec_int"
                                                     ["readln" :token/integer-TYPE]  "read_int"
                                                     ["write" :token/integer-TYPE]   "write_int"
                                                     ["write" :string-TYPE]          "write_str"
                                                     ["writeln" :token/integer-TYPE] "writeln_int"
                                                     ["writeln" :string-TYPE]        "write_str"}
                                       :forwards    {}
                                       :functions   {}
                                       :idents      #{"write" "writeln"}
                                       :return-type nil
                                       :vars        {}})))

(defn try-analyze [expr]
  (try (analyze expr)
       (catch ExceptionInfo e
         (binding [*out* *err*]
           (println (str (.getMessage e) ": " (ex-data e)))))))

(doseq [^File file (concat (.listFiles (File. "bad-ana")))]
  (try (analyze (parser/parse-file file))
       (println "Exception not handled:" (.getName file))
       (catch ExceptionInfo _OK)
       (catch Exception e
         (println (.getName file) "== runtime error ==" (.getMessage e)))))

(doseq [^File file (.listFiles (File. "samples"))]
  (try (analyze (parser/parse-file file))
       (catch ExceptionInfo e
         (binding [*out* *err*]
           (println "Analyze failed:" (.getName file) "-" (str (.getMessage e) ": " (ex-data e)))))
       (catch Exception e
         (println (.getName file) "== runtime error ==" (.getMessage e)))))
