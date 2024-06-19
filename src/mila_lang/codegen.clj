(ns mila-lang.codegen
  (:require [clojure.java.shell :as sh]
            [clojure.string :as str]
            [mila-lang.parser.core :as parser])
  (:import (clojure.lang ExceptionInfo)
           (java.io File)
           (mila_lang.parser.proto CArithmAdd
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
                                   CCmpGe
                                   CCmpGt
                                   CCmpLe
                                   CCmpLt
                                   CCmpNe
                                   CConst
                                   CDowntoFor
                                   CIfElse
                                   CIndexOp
                                   CInteger
                                   CProgram
                                   CString
                                   CSymbol
                                   CToFor
                                   CVarDecl
                                   CWhile)
           (org.bytedeco.javacpp BytePointer PointerPointer)
           (org.bytedeco.llvm.LLVM LLVMBuilderRef LLVMContextRef LLVMModuleRef LLVMTypeRef LLVMValueRef)
           (org.bytedeco.llvm.global LLVM)))

(defrecord GenContext [^LLVMContextRef context
                       ^LLVMBuilderRef builder
                       ^LLVMModuleRef module
                       table-of-symbols
                       ret-IR
                       ret-clj-type])

(defn ^LLVMTypeRef get-llvm-type [^LLVMContextRef ctx clj-type]
  (case clj-type
    :token/integer-TYPE (LLVM/LLVMInt32TypeInContext ctx)
    :token/int-pointer-TYPE (LLVM/LLVMPointerType (LLVM/LLVMInt32TypeInContext ctx) 0)
    :string-TYPE (LLVM/LLVMPointerType (LLVM/LLVMInt8TypeInContext ctx) 0)
    :void-TYPE (LLVM/LLVMVoidTypeInContext ctx)
    (throw (ex-info "Unknown call type" {:type clj-type}))))

(defn wrap-pointer-type [clj-type]
  (case clj-type
    :token/integer-TYPE :token/int-pointer-TYPE
    :string-TYPE :string-TYPE
    :void-TYPE :void-TYPE
    (throw (ex-info "Cannot wrap pointer type" {:type clj-type}))))

(defn unwrap-pointer-type&value [clj-type ^LLVMBuilderRef builder ^LLVMContextRef context ^LLVMValueRef llvm-IR]
  (case clj-type
    :token/integer-TYPE [:token/integer-TYPE llvm-IR]
    :token/int-pointer-TYPE [:token/integer-TYPE (LLVM/LLVMBuildLoad2 builder (get-llvm-type context :token/integer-TYPE) llvm-IR "")]
    :string-TYPE [:string-TYPE llvm-IR]
    (throw (ex-info "Cannot unwrap pointer value" {:clj-type clj-type}))))

(defn ^LLVMValueRef get-initial-llvm-value [clj-type ^LLVMTypeRef llvm-type]
  (case clj-type
    :token/integer-TYPE (LLVM/LLVMConstInt llvm-type 0 0)
    :void-TYPE (throw (ex-info "Cannot have a variable of void type" {}))
    (throw (ex-info "Unknown type for variable declaration" {:clj-type clj-type}))))

(defn pointer-arg-function? [target]
  (#{"read_int" "dec_int" "inc_int"} target))

(defn with-context [^String module-name f]
  (with-open [context (LLVM/LLVMContextCreate)]
    (let [module (LLVM/LLVMModuleCreateWithNameInContext module-name context)]
      (with-open [builder (LLVM/LLVMCreateBuilderInContext context)]
        (f (GenContext. context builder module {"write_int"   #:symbol{:kind :symbol-kind/function :type :void-TYPE}
                                                "write_str"   #:symbol{:kind :symbol-kind/function :type :void-TYPE}
                                                "writeln_int" #:symbol{:kind :symbol-kind/function :type :void-TYPE}
                                                "writeln_str" #:symbol{:kind :symbol-kind/function :type :void-TYPE}
                                                "dec_int"     #:symbol{:kind :symbol-kind/function :type :void-TYPE}
                                                "inc_int"     #:symbol{:kind :symbol-kind/function :type :void-TYPE}
                                                "read_int"    #:symbol{:kind :symbol-kind/function :type :void-TYPE}}
                        nil nil))))))

(defmacro keymap [& keys]
  `(hash-map ~@(mapcat #(list (keyword %) %) keys)))

(def ^:const ^String FN-DEC-INT "dec_int")
(def ^:const ^String FN-INC-INT "inc_int")
(def ^:const ^String READ-INT "read_int")
(def ^:const ^String WRITE-INT "write_int")
(def ^:const ^String WRITE-STR "write_str")
(def ^:const ^String WRITELN-INT "writeln_int")
(def ^:const ^String WRITELN-STR "writeln_str")

(defn ^LLVMValueRef generate-global-string [^LLVMModuleRef module ^LLVMContextRef context ^String value var-name]
  (let [^String var-name (or var-name (str "str_ptr_" (System/nanoTime)))
        str-len (inc (count value))
        str-type (LLVM/LLVMArrayType (LLVM/LLVMInt8TypeInContext context) str-len)
        str-const (LLVM/LLVMConstStringInContext context value (count value) 0)
        global-var (LLVM/LLVMAddGlobal module str-type var-name)]
    (LLVM/LLVMSetInitializer global-var str-const)
    global-var))

(defprotocol IConstType
  (-const-type [this] "Returns a Clojure keyword representing a record's type"))

(extend-protocol IConstType
  CString
  (-const-type [_] :string-TYPE)
  CInteger
  (-const-type [_] :token/integer-TYPE))

(defprotocol IStringy
  (stringy? [this sym-table] "Returns true iff the expression can hold a string inside."))

(extend-protocol IStringy
  CConst
  (stringy? [this _] (instance? CString (.-rhs this)))

  CVarDecl
  (stringy? [this _] (= (.-type this) :string-TYPE))

  CSymbol
  (stringy? [this sym-table] (-> this .-value sym-table :symbol/type (= :string-TYPE)))

  CString
  (stringy? [_ _] true)

  CIndexOp
  (stringy? [this sym-table] (let [type (-> this .-arr-name sym-table)]
                               (if (instance? CArrayType type)
                                 (= (.-type ^CArrayType type) :string-TYPE)
                                 (= type :string-TYPE))))

  nil
  (stringy? [_ _] false)

  Object
  (stringy? [_ _] false))

(defn coerce-extern [fname raw-args sym-table]
  (case fname
    "write" (if (and (= (count raw-args) 1)
                     (stringy? (first raw-args) sym-table))
              "write_str"
              "write_int")
    "writeln" (if (and (= (count raw-args) 1)
                       (stringy? (first raw-args) sym-table))
                "writeln_str"
                "writeln_int")
    "readln" "read_int"
    "dec" "dec_int"
    "inc" "inc_int"
    fname))

(defn- prepare-context [module-name]
  (with-context module-name (fn [^GenContext gen-ctx]
                              (let [void-type (LLVM/LLVMVoidTypeInContext (.-context gen-ctx))
                                    int-type (LLVM/LLVMInt32TypeInContext (.-context gen-ctx))
                                    int-ptr-type (LLVM/LLVMPointerType int-type 0)
                                    char-ptr-type (LLVM/LLVMPointerType (LLVM/LLVMInt8TypeInContext (.-context gen-ctx)) 0)
                                    fn-type-int (LLVM/LLVMFunctionType void-type
                                                                       (doto (PointerPointer. 1)
                                                                         (.put int-type))
                                                                       1
                                                                       0)
                                    fn-type-intptr (LLVM/LLVMFunctionType void-type
                                                                          (doto (PointerPointer. 1)
                                                                            (.put int-ptr-type))
                                                                          1
                                                                          0)
                                    fn-type-charptr (LLVM/LLVMFunctionType void-type
                                                                           (doto (PointerPointer. 1)
                                                                             (.put char-ptr-type))
                                                                           1
                                                                           0)
                                    ^LLVMModuleRef module (.-module gen-ctx)
                                    dec-int-fn (LLVM/LLVMAddFunction module FN-DEC-INT fn-type-intptr)
                                    inc-int-fn (LLVM/LLVMAddFunction module FN-INC-INT fn-type-intptr)
                                    read-int-fn (LLVM/LLVMAddFunction module READ-INT fn-type-intptr)
                                    write-int-fn (LLVM/LLVMAddFunction module WRITE-INT fn-type-int)
                                    write-str-fn (LLVM/LLVMAddFunction module WRITE-STR fn-type-charptr)
                                    writeln-int-fn (LLVM/LLVMAddFunction module WRITELN-INT fn-type-int)
                                    writeln-str-fn (LLVM/LLVMAddFunction module WRITELN-STR fn-type-charptr)
                                    exit-fn (LLVM/LLVMAddFunction module "exit" fn-type-int)]
                                (assoc gen-ctx :externs (keymap dec-int-fn inc-int-fn read-int-fn write-int-fn
                                                                write-str-fn writeln-int-fn writeln-str-fn exit-fn))))))

(def ^:dynamic *main-block* false)
(defprotocol ICodegen
  (-codegen [this ^GenContext gen-context]))

(defn ->>codegen [gen-ctx blocks]
  (reduce #(-codegen %2 %1) gen-ctx blocks))

(defn ^LLVMValueRef force-codegen-int [value ^GenContext gen-ctx]
  (let [{:keys [^LLVMValueRef ret-IR ret-clj-type] :as ^GenContext gen-ctx} (-codegen value gen-ctx)]
    (case ret-clj-type
      :token/integer-TYPE ret-IR
      :token/int-pointer-TYPE (LLVM/LLVMBuildLoad2 ^LLVMBuilderRef (.-builder gen-ctx) (get-llvm-type ^LLVMContextRef (.-context gen-ctx) :token/integer-TYPE) ret-IR "")
      (throw (ex-info "Cannot force unwrapping int pointer - not an int or int pointer" {:actual-type ret-clj-type})))))

(extend-type CProgram
  ICodegen
  (-codegen [{:keys [program-blocks main-block]} ^GenContext gen-ctx]
    (let [^GenContext gen-ctx (->>codegen gen-ctx program-blocks)
          int-type (LLVM/LLVMInt32TypeInContext (.-context gen-ctx))
          f (LLVM/LLVMAddFunction ^LLVMModuleRef (.-module gen-ctx) "main" (LLVM/LLVMFunctionType int-type
                                                                                                  (doto (PointerPointer. 1)
                                                                                                    (.put int-type))
                                                                                                  1
                                                                                                  0))
          main-llvm-basic-block (LLVM/LLVMAppendBasicBlockInContext ^LLVMContextRef (.-context gen-ctx) f "entry")]
      (LLVM/LLVMPositionBuilderAtEnd (.-builder gen-ctx) main-llvm-basic-block)
      (binding [*main-block* true]
        (-codegen main-block gen-ctx))
      (let [ret-val (LLVM/LLVMConstInt (LLVM/LLVMInt32TypeInContext (.-context gen-ctx)) 0 0)]
        (LLVM/LLVMBuildRet (.-builder gen-ctx) ret-val))
      gen-ctx)))

(extend-type CBeginEndBlock
  ICodegen
  (-codegen [{:keys [blocks]} ^GenContext gen-ctx]
    (->>codegen gen-ctx blocks)))

(extend-type CCall
  ICodegen
  (-codegen [{:keys [target args]} ^GenContext gen-ctx]
    (let [target (coerce-extern target args (.-table-of-symbols gen-ctx))
          ^LLVMContextRef context (.-context gen-ctx)
          ^LLVMModuleRef module (.-module gen-ctx)
          ^LLVMBuilderRef builder (.-builder gen-ctx)]
      (if-let [^LLVMValueRef f (LLVM/LLVMGetNamedFunction ^LLVMModuleRef module ^String target)]
        (let [codegens (map #(let [{:keys [ret-IR ret-clj-type]} (-codegen % gen-ctx)]
                               (if (pointer-arg-function? target)
                                 [ret-clj-type ret-IR]
                                 (unwrap-pointer-type&value ret-clj-type builder context ret-IR))) args)
              ^"[Lorg.bytedeco.llvm.LLVM.LLVMValueRef;" arg-vals (into-array LLVMValueRef (map second codegens))
              arg-types (PointerPointer. ^"[Lorg.bytedeco.llvm.LLVM.LLVMValueRef;" (into-array (map #(->> %
                                                                                                          first
                                                                                                          (get-llvm-type context)) codegens)))
              return-type (:symbol/type ((.-table-of-symbols gen-ctx) target))]
          (assoc gen-ctx :ret-IR (LLVM/LLVMBuildCall2 builder
                                                      (LLVM/LLVMFunctionType (get-llvm-type context return-type)
                                                                             arg-types
                                                                             (count codegens)
                                                                             0)
                                                      f
                                                      (PointerPointer. arg-vals)
                                                      (count arg-vals)
                                                      "")))
        (throw (ex-info (str "Function '" target "' is not declared in this context.") {}))))))

(extend-type CString
  ICodegen
  (-codegen [{:keys [value]} ^GenContext gen-ctx]
    (let [^LLVMContextRef context (.-context gen-ctx)
          ^LLVMBuilderRef builder (.-builder gen-ctx)
          ^LLVMModuleRef module (.-module gen-ctx)
          str-global (generate-global-string module context value (:var-name gen-ctx))
          str-type (LLVM/LLVMArrayType (LLVM/LLVMInt8TypeInContext context) (inc (count value)))
          ^"[Lorg.bytedeco.llvm.LLVM.LLVMValueRef;" indices (into-array LLVMValueRef [(LLVM/LLVMConstInt (LLVM/LLVMInt32TypeInContext context) 0 0)
                                                                                      (LLVM/LLVMConstInt (LLVM/LLVMInt32TypeInContext context) 0 0)])]
      (assoc gen-ctx :ret-IR (LLVM/LLVMBuildGEP2 builder str-type str-global (PointerPointer. indices) 2 "str_ptr")
                     :ret-clj-type :string-TYPE))))

(extend-type CInteger
  ICodegen
  (-codegen [{:keys [value]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMConstInt (LLVM/LLVMInt32TypeInContext (.-context gen-ctx)) value 1)
                   :ret-clj-type :token/integer-TYPE)))     ; signed?

(extend-type CArithmAdd
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildAdd ^LLVMBuilderRef (.-builder gen-ctx)
                                              (force-codegen-int lhs gen-ctx)
                                              (force-codegen-int rhs gen-ctx)
                                              "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmSub
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildSub ^LLVMBuilderRef (.-builder gen-ctx)
                                              (force-codegen-int lhs gen-ctx)
                                              (force-codegen-int rhs gen-ctx)
                                              "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmMul
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildMul ^LLVMBuilderRef (.-builder gen-ctx)
                                              (force-codegen-int lhs gen-ctx)
                                              (force-codegen-int rhs gen-ctx)
                                              "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmDiv
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildSDiv ^LLVMBuilderRef (.-builder gen-ctx)
                                               (force-codegen-int lhs gen-ctx)
                                               (force-codegen-int rhs gen-ctx)
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmMod
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildSRem ^LLVMBuilderRef (.-builder gen-ctx)
                                               (force-codegen-int lhs gen-ctx)
                                               (force-codegen-int rhs gen-ctx)
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmUnNeg
  ICodegen
  (-codegen [{:keys [val]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildNeg ^LLVMBuilderRef (.-builder gen-ctx)
                                              (force-codegen-int val gen-ctx)
                                              "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpLt
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntSLT
                                               (force-codegen-int lhs gen-ctx)
                                               (force-codegen-int rhs gen-ctx)
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpLe
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntSLE
                                               (force-codegen-int lhs gen-ctx)
                                               (force-codegen-int rhs gen-ctx)
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpGt
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntSGT
                                               (force-codegen-int lhs gen-ctx)
                                               (force-codegen-int rhs gen-ctx)
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpGe
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntSGE
                                               (force-codegen-int lhs gen-ctx)
                                               (force-codegen-int rhs gen-ctx)
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpEq
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntEQ
                                               (force-codegen-int lhs gen-ctx)
                                               (force-codegen-int rhs gen-ctx)
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpNe
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntNE
                                               (force-codegen-int lhs gen-ctx)
                                               (force-codegen-int rhs gen-ctx)
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CIfElse
  ICodegen
  (-codegen [{:keys [cond then else]} ^GenContext gen-ctx]
    (let [^LLVMContextRef context (.-context gen-ctx)
          ^LLVMBuilderRef builder (.-builder gen-ctx)
          ^LLVMValueRef cond-IR (:ret-IR (-codegen cond gen-ctx))
          current-block (LLVM/LLVMGetInsertBlock builder)
          current-fn (LLVM/LLVMGetBasicBlockParent current-block)
          then-block (LLVM/LLVMAppendBasicBlockInContext context current-fn "cond_then")
          else-block (LLVM/LLVMAppendBasicBlockInContext context current-fn "cond_else")
          merge-block (LLVM/LLVMAppendBasicBlockInContext context current-fn "cond_merge")]
      (LLVM/LLVMBuildCondBr builder cond-IR then-block else-block)

      (LLVM/LLVMPositionBuilderAtEnd builder then-block)
      (-codegen then gen-ctx)
      (when-not (LLVM/LLVMGetBasicBlockTerminator (LLVM/LLVMGetInsertBlock builder)) ; does not end with "ret" instruction or similar
        (LLVM/LLVMBuildBr builder merge-block))

      (LLVM/LLVMPositionBuilderAtEnd builder else-block)
      (-codegen else gen-ctx)
      (when-not (LLVM/LLVMGetBasicBlockTerminator (LLVM/LLVMGetInsertBlock builder))
        (LLVM/LLVMBuildBr builder merge-block))

      (LLVM/LLVMPositionBuilderAtEnd builder merge-block)
      (assoc gen-ctx :ret-IR nil :ret-clj-type nil))))

(extend-type CVarDecl
  ICodegen
  (-codegen [{:keys [vars type]} ^GenContext gen-ctx]
    (let [^LLVMContextRef context (.-context gen-ctx)
          ^LLVMModuleRef module (.-module gen-ctx)
          llvm-var-type (get-llvm-type context type)
          initial-value (get-initial-llvm-value type llvm-var-type)
          updated-table (reduce (fn [table ^String var-name]
                                  (if (contains? table var-name)
                                    (throw (ex-info "Symbol is already defined in this context." {:symbol-name var-name}))
                                    (let [global-var (LLVM/LLVMAddGlobal module llvm-var-type var-name)]
                                      (LLVM/LLVMSetInitializer global-var initial-value)
                                      (assoc table var-name #:symbol{:kind :symbol-kind/variable
                                                                     :type type}))))
                                (.-table-of-symbols gen-ctx)
                                vars)]
      (assoc gen-ctx :table-of-symbols updated-table))))

(extend-type CConst
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (let [{:keys [ret-IR]} (-codegen rhs (assoc gen-ctx :var-name lhs))]
      (if (contains? (.-table-of-symbols gen-ctx) lhs)
        (throw (ex-info "Symbol is already defined in this context." {:symbol-name lhs}))
        (update gen-ctx :table-of-symbols assoc lhs #:symbol{:kind   :symbol-kind/constant
                                                             :type   (-const-type rhs)
                                                             :getter ret-IR})))))

(extend-type CAssignment
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (if-let [sym ((.-table-of-symbols gen-ctx) lhs)]
      (if (= (:symbol/kind sym) :symbol-kind/variable)
        (let [{:keys [ret-IR ret-clj-type]} (-codegen rhs gen-ctx)]
          (let [^LLVMModuleRef module (.-module gen-ctx)
                ^LLVMBuilderRef builder (.-builder gen-ctx)
                ^LLVMContextRef context (.-context gen-ctx)]
            (if-let [global-var (LLVM/LLVMGetNamedGlobal module ^String lhs)]
              (do (LLVM/LLVMBuildStore builder (second (unwrap-pointer-type&value ret-clj-type builder context ret-IR)) global-var)
                  gen-ctx)
              (throw (ex-info "Global variable not found" {:symbol-name lhs})))))
        (throw (ex-info "Cannot assign to a non-variable" {:symbol-name lhs
                                                           :symbol-kind (:symbol/kind sym)})))
      (throw (ex-info "Cannot assign to symbol, not declared in the context" {:symbol-name lhs})))))

(extend-type CSymbol
  ICodegen
  (-codegen [{:keys [value]} ^GenContext gen-ctx]
    (if-let [sym ((.-table-of-symbols gen-ctx) value)]
      (case (:symbol/kind sym)
        :symbol-kind/variable (let [^LLVMModuleRef module (.-module gen-ctx)]
                                (if-let [^LLVMValueRef global-var (LLVM/LLVMGetNamedGlobal module ^String value)]
                                  (assoc gen-ctx :ret-IR global-var
                                                 :ret-clj-type (wrap-pointer-type (:symbol/type sym)))
                                  (throw (ex-info "Global variable not found" {:symbol-name value}))))
        :symbol-kind/constant (assoc gen-ctx :ret-IR (:symbol/getter sym)
                                             :ret-clj-type (:symbol/type sym))
        (throw (ex-info "Symbol is not a variable" {:symbol-name value
                                                    :symbol-kind (:symbol/kind sym)})))
      (throw (ex-info "Symbol not declared in the context" {:symbol-name value})))))

(extend-type CWhile
  ICodegen
  (-codegen [{:keys [cond body]} ^GenContext gen-ctx]
    (let [^LLVMContextRef context (.-context gen-ctx)
          ^LLVMBuilderRef builder (.-builder gen-ctx)
          function (LLVM/LLVMGetBasicBlockParent (LLVM/LLVMGetInsertBlock builder))
          cond-block (LLVM/LLVMAppendBasicBlockInContext context function "while_cond")
          body-block (LLVM/LLVMAppendBasicBlockInContext context function "while_body")
          exit-block (LLVM/LLVMAppendBasicBlockInContext context function "while_exit")]
      ; if (cond)
      (LLVM/LLVMBuildBr builder cond-block)
      (LLVM/LLVMPositionBuilderAtEnd builder cond-block)
      (let [{:keys [ret-IR]} (-codegen cond gen-ctx)]
        (LLVM/LLVMBuildCondBr builder ret-IR body-block exit-block))
      ; then
      (LLVM/LLVMPositionBuilderAtEnd builder body-block)
      (-codegen body gen-ctx)
      (LLVM/LLVMBuildBr builder cond-block)
      ; end
      (LLVM/LLVMPositionBuilderAtEnd builder exit-block)
      gen-ctx)))

(defn gen-for-loop [iter-var iter-var-init iter-var-end body ^GenContext gen-ctx is-downto?]
  (let [^LLVMContextRef context (.-context gen-ctx)
        ^LLVMBuilderRef builder (.-builder gen-ctx)
        function (LLVM/LLVMGetBasicBlockParent (LLVM/LLVMGetInsertBlock builder))
        init-block (LLVM/LLVMAppendBasicBlockInContext context function "for_init")
        cond-block (LLVM/LLVMAppendBasicBlockInContext context function "for_cond")
        body-block (LLVM/LLVMAppendBasicBlockInContext context function "for_body")
        loop-block (LLVM/LLVMAppendBasicBlockInContext context function "for_loop")
        exit-block (LLVM/LLVMAppendBasicBlockInContext context function "for_exit")
        break-cond (if is-downto?
                     (CCmpGt. (CSymbol. iter-var) iter-var-end)
                     (CCmpLt. (CSymbol. iter-var) iter-var-end))
        loop-inc-expr (if is-downto?
                        (CArithmSub. (CSymbol. iter-var) (CInteger. 1))
                        (CArithmAdd. (CSymbol. iter-var) (CInteger. 1)))]
    ; init var
    (LLVM/LLVMBuildBr builder init-block)
    (LLVM/LLVMPositionBuilderAtEnd builder init-block)
    (-codegen (CAssignment. iter-var iter-var-init) gen-ctx)
    (LLVM/LLVMBuildBr builder cond-block)
    ; if (cond)
    (LLVM/LLVMPositionBuilderAtEnd builder cond-block)
    (let [{:keys [ret-IR]} (-codegen break-cond gen-ctx)]
      (LLVM/LLVMBuildCondBr builder ret-IR body-block exit-block))
    ; then
    (LLVM/LLVMPositionBuilderAtEnd builder body-block)
    (-codegen body gen-ctx)
    (LLVM/LLVMBuildBr builder loop-block)
    ; inc var
    (LLVM/LLVMPositionBuilderAtEnd builder loop-block)
    (-codegen (CAssignment. iter-var loop-inc-expr) gen-ctx)
    (LLVM/LLVMBuildBr builder cond-block)
    ; end
    (LLVM/LLVMPositionBuilderAtEnd builder exit-block)
    gen-ctx))

(extend-type CToFor
  ICodegen
  (-codegen [{:keys [iter-var iter-var-init iter-var-end body]} ^GenContext gen-ctx]
    (gen-for-loop iter-var iter-var-init iter-var-end body gen-ctx false)))

(extend-type CDowntoFor
  ICodegen
  (-codegen [{:keys [iter-var iter-var-init iter-var-end body]} ^GenContext gen-ctx]
    (gen-for-loop iter-var iter-var-init iter-var-end body gen-ctx true)))

(defmacro ->err [& body]
  `(binding [*out* *err*]
     ~@body))

(defn verify-module [^GenContext gen-ctx]
  (let [error (BytePointer.)]
    (if (zero? (LLVM/LLVMVerifyModule ^LLVMModuleRef (.-module gen-ctx) LLVM/LLVMPrintMessageAction error))
      (LLVM/LLVMDisposeMessage error)
      (let [fname (str "log-" (System/currentTimeMillis) ".txt")]
        (do (println "Failed to verify module. Dumping to " fname)
            (LLVM/LLVMPrintModuleToFile ^LLVMModuleRef (.-module gen-ctx) fname error)
            (throw (ex-info (str "Failed building LLVM IR: " (.getString error)) {})))))))

(defn write-module-to-file [^GenContext gen-ctx ^String filename]
  (LLVM/LLVMPrintModuleToFile ^LLVMModuleRef (.-module gen-ctx) filename (BytePointer.)))

(defn codegen [source-file out-file]
  (let [^CProgram program-ast (try (parser/parse-file source-file)
                                   (catch ExceptionInfo e
                                     (->err
                                       (printf "Failed to parse file '%s': %s\n" source-file (.getMessage e)))
                                     (throw e)))
        gen-ctx (prepare-context (.-program-name program-ast))
        final-ctx (-codegen program-ast gen-ctx)]
    (verify-module final-ctx)
    (write-module-to-file final-ctx out-file)))

(defmacro with-sh-err [cmd & body]
  `(let [res# ~cmd]
     (if (zero? (:exit res#))
       ~(if (<= (count body) 1)
          (first body)
          `(with-sh-err ~@body))
       (throw (ex-info (str "Could not compile program") {:err (:err res#)})))))

(def target-triple "x86_64-pc-windows-msvc")

(defn- compile-cached [^String in ^String out]
  (if (> (.lastModified (File. in)) (.lastModified (File. out)))
    (do (println "Compile" in "->" out)
        (sh/sh "clang" "-c" in "-o" out "-target" target-triple "-Wno-override-module"))
    {:exit 0}))

(defn compile-and-run [source-file IR-file out-file prog-sh-conf]
  (let [externs "externs/io.c"
        externs-out "out/io.o"]
    (codegen source-file IR-file)
    (with-sh-err
      (compile-cached externs externs-out)
      (sh/sh "clang" "-c" source-file "-o" IR-file "-target" target-triple "-Wno-override-module")
      (sh/sh "clang" IR-file externs-out "-o" out-file "-target" target-triple)
      (apply sh/sh (str "./" out-file) (apply concat prog-sh-conf)))))

(defn normalize-string
  "I. Hate. CRLF. Convention. On. Windows. It's pain to test it by exact \r\n matching, so splitting into lines is fine"
  [s]
  (->> s str/split-lines (filter seq)))

(defn run-sample [[file-name {:keys [expected] :as prog-sh-conf}]]
  (let [src-file (str "samples/" file-name ".mila")
        IR-file (str "out/" file-name ".bc")
        out-file (str "out/" file-name ".exe")]
    (let [{:keys [out]} (try (compile-and-run src-file IR-file out-file prog-sh-conf)
                             (catch Throwable t
                               (println (.getMessage t))))]
      (if (and out expected (= (normalize-string out) (normalize-string expected)))
        (println "Success:" file-name)
        (binding [*out* *err*]
          (println "Incorrect output:" file-name))))))

(defn lines [& xs]
  (str/join \newline xs))

(defn run-samples [& [files]]
  (.mkdir (File. "out"))
  (doseq [sample (or files [["arithmetics" {:expected (lines "1 + 2 = 3"
                                                             "1 - 2 = -1"
                                                             "2 * 3 = 6"
                                                             "20 / 3 = 6"
                                                             "20 % 3 = 2"
                                                             "3 * (4 + 17 % 6) - (7 / 2) = 24"
                                                             "3 * -4 = -12")}]
                            ["conditionals" {:expected (lines "1 + 1 < 2: false"
                                                              "1 + 1 <= 2: true"
                                                              "1 + 1 > 2: false"
                                                              "1 + 1 >= 2: true"
                                                              "1 + 1 == 2: true"
                                                              "1 + 1 != 2: false")}]
                            ["consts" {:expected (lines "10\n16\n8\nabcdef")}]
                            ["expressions" {:in "5" :expected "30"}]
                            ["expressions2" {:in "10 13" :expected (lines "10" "13" "23" "3" "330" "2")}]
                            ["factorialCycle" {:in "5" :expected "120"}]
                            ["for-loops" {:expected (lines "0,0"
                                                           "1,0" "1,1"
                                                           "2,0" "2,1" "2,2"
                                                           "3,0" "3,1" "3,2" "3,3"
                                                           "midpoint"
                                                           "0,0"
                                                           "1,1" "1,0"
                                                           "2,2" "2,1" "2,0"
                                                           "3,3" "3,2" "3,1" "3,0")}]
                            ["hello-42" {:expected "42"}]
                            ["hello-world" {:expected "Hello, world!"}]
                            ["inputOutput" {:in "42" :expected "42"}]
                            ["multiple-decls" {:expected "40"}]
                            ["string-test" {:expected (lines "A quote', tab\t, newline"
                                                             " and return\r.")}]
                            ["vars" {:expected (lines "x := 3, y := 4"
                                                      "x + y = 7"
                                                      "y := y * y"
                                                      "x + y = 19")}]
                            ["while-print" {:in "5" :expected (lines "5" "4" "3" "2" "1" "Happy New year!")}]])]
    (run-sample sample)))
