(ns mila-lang.parser.core
  (:require [cheshire.core :as json]
            [clojure.string :as str]
            [mila-lang.lexer.core :as lexer])
  (:import (clojure.lang ExceptionInfo)
           (java.io File)))

(def eps (keyword "ε"))

(defn parse [filename]
  (let [str->kw #(if (Character/isUpperCase ^Character (first %))
                   (keyword %)
                   (keyword "token" %))
        grammar (->> (slurp "grammar.txt")
                     str/split-lines
                     (filter seq)
                     (map-indexed (fn [i s]
                                    (let [[rule product] (map str/trim (str/split s #"->"))
                                          product (if (nil? product)
                                                    nil
                                                    (->> (str/split product #" ")
                                                         (mapv str->kw)))]
                                      [(inc i) [(keyword (str/trim rule)) product]])))
                     (into {}))
        ll1-parse-table (into (sorted-map) (json/decode (slurp "parse-table.json") str->kw))
        tokens (lexer/lex filename)
        xor (fn [x y] (if x (not y) y))]
    (loop [stack [:S]
           tokens tokens
           left-derivation []
           read-tokens []]
      (let [[e1 e2] [(empty? stack) (empty? tokens)]]
        (cond (and e1 e2)
              {:left-derivation left-derivation}

              (xor e1 e2)
              (throw (ex-info "stack or tokens not empty" {:stack           stack
                                                           :tokens          tokens
                                                           :left-derivation left-derivation
                                                           :trace           {:stack-peek (peek stack) :first-token (ffirst tokens)}
                                                           :read-tokens     read-tokens}))

              (= (ffirst tokens) (peek stack))
              (recur (pop stack) (next tokens) left-derivation (conj read-tokens (first tokens)))

              :else (if-let [rule-index (get-in ll1-parse-table [(peek stack) (ffirst tokens)])]
                      (let [[_ rule-rhs :as whole-rule] (grammar rule-index)]
                        (recur (into (pop stack) (reverse rule-rhs))
                               tokens
                               (conj left-derivation whole-rule)
                               read-tokens))
                      (throw (ex-info "Rule not found" {:stack           stack
                                                        :tokens          tokens
                                                        :left-derivation left-derivation

                                                        :read-tokens     read-tokens}))))))))

(defn parse-sample [filename] (parse (str "samples/" filename ".mila")))

(defn test-samples []
  (let [samples (File. "samples")]
    (assert (and (.exists samples) (.isDirectory samples)) "Cannot open directory 'samples'")
    (doseq [^File child (.listFiles samples)
            :when (and (str/ends-with? (.getName child) ".mila")
                       (not (str/starts-with? (.getName child) "noparse")))]
      (println "Parsing" (.getName child))
      (try (parse child)
           (println "Success!")
           (catch ExceptionInfo _
             (binding [*out* *err*]
               (println "Error parsing" (.getName child))))))))