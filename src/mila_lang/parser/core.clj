(ns mila-lang.parser.core
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [clojure.edn :as edn]
            [clojure.walk :as walk]
            [mila-lang.lexer.core :as lexer]
            [mila-lang.parser.proto :as p])
  (:import (clojure.lang ExceptionInfo)
           (java.awt Toolkit)
           (java.awt.datatransfer StringSelection)
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
                                   CBoolean
                                   CBreak
                                   CCall
                                   CCmpEq
                                   CCmpGt
                                   CCmpGe
                                   CCmpLt
                                   CCmpLe
                                   CCmpNe
                                   CConst
                                   CContinue
                                   CDowntoFor
                                   CExit
                                   CFloat
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

(def eps (keyword "ε"))

(defn copy [s]
  (.. (Toolkit/getDefaultToolkit)
      (getSystemClipboard)
      (setContents (StringSelection. s) nil)))

(def char-at mila-lang.lexer.base/char-at)

(def m {})

(defn match [[token-queue token]]
  (when (not= (ffirst token-queue) token)
    (throw (ex-info "Match failed" {:expected        token
                                    :actual          (ffirst token-queue)
                                    :remaining-queue token-queue})))
  [(next token-queue) (second (first token-queue))])

(def str->kw #(if (Character/isUpperCase ^Character (first %))
                (keyword %)
                (keyword "token" %)))

(defn transform [form]
  (walk/postwalk
    (fn [x]
      (if (and (symbol? x)
               (and (Character/isUpperCase ^Character (char-at (name x) 0))
                    (not (identical? (char-at (name x) (dec (.length (name x)))) \.))))
        (list #'m (keyword x))
        x))

    form))

(defn create-function-mappings [grammar-file parse-table-file]
  (let [expr-parse-table (json/decode (slurp parse-table-file) str->kw)]
    (->> (slurp grammar-file)
         edn/read-string
         (map-indexed (fn [i [lhs f]]
                        [(keyword (first (str/split lhs #" ->"))) (inc i) (transform f)]))
         (group-by first)
         (map (fn [[lhs xs]]
                [lhs (mapv next xs)]))
         (map (fn [[lhs xs]]
                [lhs
                 (let [fn-parse-table-functions (into {} (map (fn [[i f]]
                                                                [i (eval f)]))
                                                      xs)]
                   (fn [[[[next-token] :as rst-tokens] :as args]]
                     (if-let [rule-index (get-in expr-parse-table [lhs next-token])]
                       ((fn-parse-table-functions rule-index) args)
                       (throw (ex-info "Could not find rule in the parse table"
                                       {:non-terminal lhs
                                        :next-token   next-token
                                        :rst-tokens   rst-tokens})))))]))
         (into {}))))

#_(alter-var-root #'m (constantly (create-function-mappings "expr-grammar.edn" "expr-grammar-parse-table.json")))
(alter-var-root #'m (constantly (create-function-mappings "attributed-grammar.edn" "parse-table.json")))

(defn parse-file [file]
  ((m :S) [(lexer/lex file)]))

(defn parse* [input]
  ((m :S) [(mila-lang.lexer.base/lex* input)]))

(defn try-parse-file [expr]
  (try (parse-file expr)
       (catch ExceptionInfo e
         (binding [*out* *err*]
           (println (str (.getMessage e) ": " (ex-data e)))))))

(defn copy-grammar []
  (->> (slurp "attributed-grammar.edn")
       edn/read-string
       (map first)
       (str/join "\n")
       copy))

(defn parse-samples []
  (let [samples (File. "samples")]
    (assert (and (.exists samples) (.isDirectory samples)) "Cannot open directory 'samples'")
    (doseq [^File child (.listFiles samples)
            :when (and (str/ends-with? (.getName child) ".mila")
                       (not (str/starts-with? (.getName child) "noparse")))]
      (try (parse-file child)
           (println "Success parsing" (.getName child))
           (catch ExceptionInfo _
             (binding [*out* *err*]
               (println "Error parsing" (.getName child))))))))

(time (parse-samples))
