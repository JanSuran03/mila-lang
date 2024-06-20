(ns mila-lang.lexer.test
  (:require [mila-lang.lexer.base :as lexer]
            [mila-lang.lexer.impl]))

(defmacro expect-error [form]
  `(when-not
     (try ~form
          false
          (catch IndexOutOfBoundsException _#
            (throw _#)
            false)
          (catch RuntimeException _#
            true))
     (throw (RuntimeException. ~(str "Expected throw for form: " form)))))

(defn assert-lex [str expected-tokens]
  (assert (= (lexer/lex* str) expected-tokens)))

(def tests [{:input  "program prg; begin writeln('foo') end."
             :tokens [[:token/program]
                      [:token/symbol "prg"]
                      [:token/semicolon]
                      [:token/begin]
                      [:token/symbol "writeln"]
                      [:token/lparen]
                      [:token/string "foo"]
                      [:token/rparen]
                      [:token/end]
                      [:token/dot]
                      [:token/eof]]}
            {:input  "program _;"
             :tokens [[:token/program]
                      [:token/symbol "_"]
                      [:token/semicolon]
                      [:token/eof]]}
            {:input  "123"
             :tokens [[:token/number 123]
                      [:token/eof]]}
            {:input  "$21"
             :tokens [[:token/number 33]
                      [:token/eof]]}
            {:input  "&21"
             :tokens [[:token/number 17]
                      [:token/eof]]}
            {:input  "-2"
             :tokens [[:token/sub]
                      [:token/number 2]
                      [:token/eof]]}
            {:input  "abc"
             :tokens [[:token/symbol "abc"]
                      [:token/eof]]}
            {:input  "a:b"
             :tokens [[:token/symbol "a"]
                      [:token/colon]
                      [:token/symbol "b"]
                      [:token/eof]]}
            {:input  "a;b"
             :tokens [[:token/symbol "a"]
                      [:token/semicolon]
                      [:token/symbol "b"]
                      [:token/eof]]}
            {:input  "a.b"
             :tokens [[:token/symbol "a"]
                      [:token/dot]
                      [:token/symbol "b"]
                      [:token/eof]]}
            {:input  "a..b"
             :tokens [[:token/symbol "a"]
                      [:token/dotdot]
                      [:token/symbol "b"]
                      [:token/eof]]}
            {:input  "."
             :tokens [[:token/dot]
                      [:token/eof]]}])

(def wrong-inputs ["2a"
                   "program2$"
                   "'abc\\x'"
                   "'abc"
                   "^a"
                   "ab@c"])

(defn run-tests []
  (doseq [{:keys [input tokens]} tests]
    (assert-lex input tokens))
  (doseq [wrong-input wrong-inputs]
    (expect-error (lexer/lex* wrong-input))))

(run-tests)
