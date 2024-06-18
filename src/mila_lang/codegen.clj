(ns mila-lang.codegen
  (:require [clojure.java.shell :as sh]
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
                                   CBeginEndBlock
                                   CCall
                                   CCmpEq
                                   CCmpGe
                                   CCmpGt
                                   CCmpLe
                                   CCmpLt
                                   CCmpNe
                                   CConst
                                   CIfElse
                                   CIndexOp
                                   CInteger
                                   CProgram
                                   CString
                                   CSymbol
                                   CVarDecl)
           (org.bytedeco.javacpp BytePointer PointerPointer)
           (org.bytedeco.llvm.LLVM LLVMBuilderRef LLVMContextRef LLVMModuleRef LLVMTypeRef LLVMValueRef)
           (org.bytedeco.llvm.global LLVM)))

(defrecord GenContext [^LLVMContextRef context
                       ^LLVMBuilderRef builder
                       ^LLVMModuleRef module
                       table-of-symbols
                       ret-IR
                       ret-clj-type])

(defn ^LLVMTypeRef call-type [^LLVMContextRef ctx clj-type]
  (case clj-type
    :token/integer-TYPE (LLVM/LLVMInt32TypeInContext ctx)
    :string-TYPE (LLVM/LLVMPointerType (LLVM/LLVMInt8TypeInContext ctx) 0)
    :void-TYPE (LLVM/LLVMVoidTypeInContext ctx)
    (throw (ex-info "Unknown call type" {:actual clj-type}))))

(defn with-context [^String module-name f]
  (with-open [context (LLVM/LLVMContextCreate)]
    (let [module (LLVM/LLVMModuleCreateWithNameInContext module-name context)]
      (with-open [builder (LLVM/LLVMCreateBuilderInContext context)]
        (f (GenContext. context builder module {"write_int"   :void-TYPE
                                                "write_str"   :void-TYPE
                                                "writeln_int" :void-TYPE
                                                "writeln_str" :void-TYPE
                                                "dec_int"     :void-TYPE
                                                "inc_int"     :void-TYPE
                                                "read_int"    :void-TYPE}
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

(defprotocol IStringy
  (stringy? [this sym-table] "Returns true iff the expression can hold a string inside."))

(extend-protocol IStringy
  CConst
  (stringy? [this _] (instance? CString (.-rhs this)))

  CVarDecl
  (stringy? [this _] (= (.-type this) :string-TYPE))

  CSymbol
  (stringy? [this sym-table] (-> this .-value sym-table (= :string-TYPE)))

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

(defn ^LLVMValueRef generate-global-string [^LLVMBuilderRef builder ^String value]
  (LLVM/LLVMBuildGlobalStringPtr builder value "str_ptr")
  #_(let [str-len (inc (.length value))                     ; include '\0' char
          str-global-name (str ".str_" (hash value))
          str-type (LLVM/LLVMArrayType (LLVM/LLVMInt8TypeInContext context) str-len)
          str-global (LLVM/LLVMAddGlobal module str-type str-global-name)]
      (LLVM/LLVMSetInitializer str-global (LLVM/LLVMConstStringInContext context value str-len 0))
      (LLVM/LLVMSetLinkage str-global LLVM/LLVMPrivateLinkage)
      (LLVM/LLVMSetGlobalConstant str-global 1)
      str-global))

(extend-type CProgram
  ICodegen
  (-codegen [{:keys [program-blocks main-block]} ^GenContext gen-ctx]
    #_(->>codegen gen-ctx program-blocks)
    (let [int-type (LLVM/LLVMInt32TypeInContext (.-context gen-ctx))
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
        (let [codegens (map #(-codegen % gen-ctx) args)
              ^"[Lorg.bytedeco.llvm.LLVM.LLVMValueRef;" arg-vals (into-array LLVMValueRef (map :ret-IR codegens))
              arg-types (PointerPointer. ^"[Lorg.bytedeco.llvm.LLVM.LLVMValueRef;" (into-array (map #(call-type context (:ret-clj-type %)) codegens)))
              return-type ((.-table-of-symbols gen-ctx) target)]
          (assoc gen-ctx :ret-IR (LLVM/LLVMBuildCall2 builder
                                                      (LLVM/LLVMFunctionType (call-type context return-type)
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
          ^LLVMModuleRef module (.-module gen-ctx)
          ^LLVMBuilderRef builder (.-builder gen-ctx)
          str-global (generate-global-string builder value)
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
                                              ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                              ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                              "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmSub
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildSub ^LLVMBuilderRef (.-builder gen-ctx)
                                              ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                              ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                              "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmMul
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildMul ^LLVMBuilderRef (.-builder gen-ctx)
                                              ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                              ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                              "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmDiv
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildSDiv ^LLVMBuilderRef (.-builder gen-ctx)
                                               ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                               ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmMod
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildSRem ^LLVMBuilderRef (.-builder gen-ctx)
                                               ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                               ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CArithmUnNeg
  ICodegen
  (-codegen [{:keys [val]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildNeg ^LLVMBuilderRef (.-builder gen-ctx)
                                              ^LLVMValueRef (:ret-IR (-codegen val gen-ctx))
                                              "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpLt
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntSLT
                                               ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                               ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpLe
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntSLE
                                               ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                               ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpGt
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntSGT
                                               ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                               ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpGe
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntSGE
                                               ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                               ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpEq
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntEQ
                                               ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                               ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
                                               "")
                   :ret-clj-type :token/integer-TYPE)))

(extend-type CCmpNe
  ICodegen
  (-codegen [{:keys [lhs rhs]} ^GenContext gen-ctx]
    (assoc gen-ctx :ret-IR (LLVM/LLVMBuildICmp ^LLVMBuilderRef (.-builder gen-ctx)
                                               LLVM/LLVMIntNE
                                               ^LLVMValueRef (:ret-IR (-codegen lhs gen-ctx))
                                               ^LLVMValueRef (:ret-IR (-codegen rhs gen-ctx))
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

(defn compile-and-run [source-file out-file]
  (let [IR-file (str (.getName (File. ^String source-file)) ".bc")
        externs "externs/io.c"
        externs-out "externs/io.o"]
    (codegen source-file IR-file)
    (with-sh-err
      (compile-cached externs externs-out)
      (sh/sh "clang" "-c" source-file "-o" IR-file "-target" target-triple "-Wno-override-module")
      (sh/sh "clang" IR-file "externs/io.o" "-o" out-file "-target" target-triple)
      (sh/sh (str "./" out-file)))))

(defn sample []
  (try (compile-and-run "samples/hello-world.mila" "hello-world.exe")
       (catch ExceptionInfo e
         (println (str "Fail ex-info (" (ex-message e) "), cause: " (ex-data e))))
       (catch Exception e
         (println "Fatal fail:" (.getMessage e))
         (.printStackTrace e))))

(defn run-sample [src-file out-file]
  (let [{:keys [out]} (compile-and-run src-file out-file)]
    (printf "./%s\n" out-file)
    (println out)))

(defn run-samples []
  (doseq [sample ["hello-42"
                  "hello-world"
                  "string-test"
                  "arithmetics"
                  "conditionals"]]
    (run-sample (str "samples/" sample ".mila") (str sample ".exe"))))
