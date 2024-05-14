(set! *warn-on-reflection* true)

(ns mila-lang.core
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [clojure.edn :as edn]
            [clojure.walk :as walk]
            [clojure.pprint :as pp]
            [mila-lang.lexer.core :as lexer]
            [mila-lang.parser.core :as parser])
  (:import (java.awt Toolkit)
           (java.awt.datatransfer StringSelection)))

(defn copy [s]
  (.. (Toolkit/getDefaultToolkit)
      (getSystemClipboard)
      (setContents (StringSelection. s) nil)))



(def char-at mila-lang.lexer.base/char-at)

(def m {})

(defn match [[token-queue token]]
  (when (not= (ffirst token-queue) token)
    (throw (ex-info "Match failed" {:expected token :actual (ffirst token-queue)})))
  [(next token-queue) (second (first token-queue))])

(def str->kw #(if (Character/isUpperCase ^Character (first %))
                (keyword %)
                (keyword "token" %)))

(defn transform [form]
  (walk/postwalk
    (fn [x]
      (if (and (symbol? x)
               (Character/isUpperCase ^Character (char-at (name x) 0)))
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
                 (let [fn-parse-table-functions (into {} (map (fn [[i f]] [i (eval f)])) xs)]
                   (fn [[[[next-token]] :as args]]
                     (if-let [rule-index (get-in expr-parse-table [lhs next-token])]
                       ((fn-parse-table-functions rule-index) args)
                       (throw (throw (ex-info "Could not find rule in the parse table"
                                              {:non-terminal lhs
                                               :next-token   next-token}))))))]))
         (into {}))))

(alter-var-root #'m (constantly (create-function-mappings "expr-grammar.edn" "expr-grammar-parse-table.json")))

(defn evaluate-expr [file]
  ((m :S) [(lexer/lex file)]))
