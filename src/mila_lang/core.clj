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

(def expr-parse-table (json/decode (slurp "expr-grammar-parse-table.json") str->kw))

(defn transform [form]
  (walk/postwalk
    (fn [x]
      (if (and (symbol? x)
               (Character/isUpperCase ^Character (char-at (name x) 0)))
        (list #'m (keyword x))
        x))

    form))

(defn evaluate-expr []
  (let [token-input (lexer/lex "samples/noparse-expr.mila")
        function-mappings (->> (slurp "expr-grammar.edn")
                               edn/read-string
                               (map-indexed (fn [i [lhs f]]
                                              [(keyword (first (str/split lhs #" ->"))) (inc i) (transform f)]))
                               (group-by first)
                               (map (fn [[lhs xs]]
                                      [lhs (mapv next xs)]))
                               (map (fn [[lhs xs]]
                                      [lhs (eval `(fn [[[[next-token#]] :as args#]]
                                                    (if-let [rule-index# (get-in ~'expr-parse-table [~lhs next-token#])]
                                                      (if-let [function# (case rule-index#
                                                                           ~@(apply concat xs))]
                                                        (function# args#)
                                                        (println "ERROR 2!" [~lhs next-token#]))
                                                      (println "ERROR 1!" [~lhs next-token#]))))])))]
    (alter-var-root #'m (constantly (into {} function-mappings)))
    ((m :S) [token-input])))
