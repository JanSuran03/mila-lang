(ns mila-lang.lexer.base
  (:refer-clojure :exclude [case]))

(defn eof? [^String input index] (>= index (.length input)))
(defn ^Character char-at [^String input index] (.charAt input index))

(defn crange [[begin end]]
  (assert (<= (int begin) (int end)))
  (map char (range (int begin) (inc (int end)))))

(defn ranges [& ranges] (mapcat crange ranges))
(def sym-start-pat (ranges "az" "AZ" "__"))
(def pos-dig-pat (crange "19"))
(def any-dig-pat (conj pos-dig-pat \0))
(def sym-char-pat (concat sym-start-pat any-dig-pat))
(def ws-pat (list \space \newline \tab \return))
(def num-base-pat (list \$ \&))
(def common-token-char-pat (seq ":<>+-*/="))
(def token-end-pat (concat ws-pat "'.,;()[]"))
(def safe-num-sym-end-pat (seq ":<>' \n\t\r.,;+-*/()[]="))

(defn invalid-token [buf]
  (throw (RuntimeException. (str "Invalid token: " buf))))

(defn char->int [ch] (- (int ch) (int \0)))

(defn hex-num [ch]
  (cond (Character/isDigit ^Character ch) (char->int ch)
        (<= (int \A) (int ch) (int \F)) (+ 10 (- (int ch) (int \A)))
        (<= (int \a) (int ch) (int \f)) (+ 10 (- (int ch) (int \a)))
        :else nil))

(defn oct-num [ch]
  (if (<= (int \0) (int ch) (int \7))
    (char->int ch)
    nil))

(defmacro case [e & clauses]
  (let [clauses (loop [ret []
                       clauses clauses]
                  (cond (empty? clauses)
                        (conj ret `(throw (RuntimeException. "No matching clause.")))

                        (nil? (next clauses))
                        (conj ret (first clauses))

                        (vector? (first clauses))
                        (recur (-> ret (conj (eval (ffirst clauses)))
                                   (conj (second clauses)))
                               (nnext clauses))

                        :else
                        (recur (-> ret (conj (first clauses))
                                   (conj (second clauses)))
                               (nnext clauses))))]
    `(clojure.core/case ~e ~@clauses)))

(defmulti lex-impl (fn [state _input _index]
                     state))

(defmethod lex-impl :lexer/default
  [_ input index]
  (if (eof? input index)
    [[:token/eof] (inc index)]
    (case (char-at input index)
      \: (lex-impl :lexer/colon input index)
      \. (lex-impl :lexer/dot input index)
      \> (lex-impl :lexer/gt input index)
      \< (lex-impl :lexer/lt input index)
      \' (lex-impl :lexer/string input index)
      \0 (lex-impl :lexer/zero input index)
      \$ (lex-impl :lexer/hex input index)
      \& (lex-impl :lexer/oct input index)
      (\space \newline \tab \return) (lex-impl :lexer/default input (inc index))
      \+ [[:token/add] (inc index)]
      \, [[:token/comma] (inc index)]
      \= [[:token/eq] (inc index)]
      \[ [[:token/lbracket] (inc index)]
      \( [[:token/lparen] (inc index)]
      \* [[:token/mul] (inc index)]
      \] [[:token/rbracket] (inc index)]
      \) [[:token/rparen] (inc index)]
      \; [[:token/semicolon] (inc index)]
      \- [[:token/sub] (inc index)]
      [sym-start-pat] (lex-impl :lexer/symbol input index)
      [pos-dig-pat] (lex-impl :lexer/int input index)
      (invalid-token (char-at input index)))))

(def word-tokens #{:token/and
                   :token/array
                   :token/begin
                   :token/const
                   :token/div
                   :token/do
                   :token/downto
                   :token/else
                   :token/end
                   :token/exit
                   :token/for
                   :token/forward
                   :token/function
                   :token/if
                   :token/mod
                   :token/of
                   :token/or
                   :token/program
                   :token/procedure
                   :token/to
                   :token/var
                   :token/while})

(defn lex* [input]
  ((fn [input index tokens]
     (if (eof? input index)
       (conj tokens [:token/eof])
       (let [[next-token next-index] (lex-impl :lexer/default input index)]
         (if (= (next-token 0) :token/eof)
           (conj tokens [:token/eof])
           (recur input next-index (conj tokens next-token))))))
   input
   0
   []))

(defn lex [file]
  (lex* (slurp file)))
