(ns mila-lang.lexer.impl
  (:refer-clojure :exclude [case])
  (:require [mila-lang.lexer.base :as lexer :refer
             [case char-at char->int eof? invalid-token]]))

(defmethod lexer/lex-impl :lexer/colon
  [_ input index]
  (let [index (inc index)]
    (if (eof? input index)
      [[:token/colon] index]
      (let [ch (char-at input index)]
        (case ch
          \= [[:token/assign] (inc index)]
          [(concat lexer/token-end-pat lexer/sym-char-pat)] [[:token/colon] index]
          (invalid-token (str \: ch)))))))

(defn- sym->?token [buf index]
  (if-let [word-token (lexer/word-tokens (keyword "token" buf))]
    [[word-token] index]
    [[:token/symbol (str buf)] index]))

(defmethod lexer/lex-impl :lexer/symbol
  [_ input index]
  (loop [buf (str (char-at input index))
         index (inc index)]
    (if (eof? input index)
      (sym->?token buf index)
      (let [ch (char-at input index)]
        (case ch
          [lexer/sym-char-pat] (recur (str buf ch)
                                      (inc index))
          [(concat lexer/safe-num-sym-end-pat ".")] (sym->?token buf index)
          (invalid-token (str buf ch)))))))

(defn lex-decimal-float-part [^Integer integer-part input index]
  (loop [value (str integer-part ".")
         index index]
    (if (eof? input index)
      [[:token/float (Double/parseDouble value)] index]
      (let [ch (char-at input index)]
        (case ch
          [lexer/any-dig-pat] (recur (str value ch)
                                     (inc index))
          [lexer/safe-num-sym-end-pat] [[:token/float (Double/parseDouble value)] index]
          (throw (RuntimeException. (str "Could not read the decimal part of a number: '" value "'"))))))))

(defmethod lexer/lex-impl :lexer/number
  [_ input index]
  (loop [value (char->int (char-at input index))
         index (inc index)]
    (if (eof? input index)
      [[:token/integer value] index]
      (let [ch (char-at input index)]
        (case ch
          [lexer/any-dig-pat] (recur (+ (* 10 value) (char->int ch))
                                     (inc index))
          [lexer/safe-num-sym-end-pat] [[:token/integer value] index]
          \. (lex-decimal-float-part value input (inc index))
          (invalid-token (str value ch)))))))

(defmethod lexer/lex-impl :lexer/dot
  [_ input index]
  (let [index (inc index)]
    (if (eof? input index)
      [[:token/dot] index]
      (let [ch (char-at input index)]
        (case ch
          \. [[:token/dotdot] (inc index)]
          [lexer/common-token-char-pat] (invalid-token (str \. ch))
          [[:token/dot] index])))))

(defmethod lexer/lex-impl :lexer/zero
  [_ input index]
  (let [index (inc index)]
    (if (eof? input index)
      [[:token/integer 0] index]
      (let [ch (char-at input index)]
        (case ch
          [lexer/safe-num-sym-end-pat] [[:token/integer 0] index]
          (invalid-token (str \0 ch)))))))

(defmethod lexer/lex-impl :lexer/hex
  [_ input index]
  (let [index (inc index)]
    (if (eof? input index)
      (invalid-token "$")
      (loop [value 0
             index index
             loaded false]
        (if (eof? input index)
          [[:token/integer value] index]
          (let [ch (char-at input index)
                as-hex (lexer/hex-num ch)]
            (when (and (not loaded)
                       (or (nil? as-hex))
                       (zero? as-hex))
              (invalid-token (str "$" ch)))
            (if as-hex
              (recur (long (+ (* value 16) as-hex)) (inc index) true)
              (case ch
                [lexer/safe-num-sym-end-pat] [[:token/integer value] index]
                (invalid-token (str "$" value ch))))))))))

(defmethod lexer/lex-impl :lexer/oct
  [_ input index]
  (let [index (inc index)]
    (if (eof? input index)
      (invalid-token "&")
      (loop [value 0
             index index
             loaded false]
        (if (eof? input index)
          [[:token/integer value] index]
          (let [ch (char-at input index)
                as-oct (lexer/oct-num ch)]
            (when (and (not loaded)
                       (or (nil? as-oct))
                       (zero? as-oct))
              (invalid-token (str "&" ch)))
            (if as-oct
              (recur (long (+ (* value 8) as-oct)) (inc index) true)
              (case ch
                [lexer/safe-num-sym-end-pat] [[:token/integer value] index]
                (invalid-token (str "&" value ch))))))))))

(defmethod lexer/lex-impl :lexer/gt
  [_ input index]
  (let [index (inc index)]
    (if (eof? input index)
      [[:token/gt] index]
      (let [ch (char-at input index)]
        (case ch
          \= [[:token/ge] (inc index)]
          [lexer/token-end-pat] [[:token/gt] index]
          (invalid-token (str ">" ch)))))))

(defmethod lexer/lex-impl :lexer/lt
  [_ input index]
  (let [index (inc index)]
    (if (eof? input index)
      [[:token/lt] index]
      (let [ch (char-at input index)]
        (case ch
          \= [[:token/le] (inc index)]
          \> [[:token/ne] (inc index)]
          [lexer/token-end-pat] [[:token/lt] index]
          (invalid-token (str "<" ch)))))))

(defn escape-char [s index]
  (case (char-at s index)
    \n \newline
    \t \tab
    \r \return
    \' \'
    \b \backspace
    nil))

(defmethod lexer/lex-impl :lexer/string
  [_ input index]
  (loop [buf ""
         index (inc index)]
    (if (eof? input index)
      (throw (RuntimeException. (str "End of file while reading string.")))
      (let [ch (char-at input index)]
        (case ch
          \' [[:token/string buf] (inc index)]
          \\ (let [index (inc index)]
               (if (eof? input index)
                 (throw (RuntimeException. (str "End of file while reading string.")))
                 (if-let [escaped (escape-char input index)]
                   (recur (str buf escaped) (inc index))
                   (throw (RuntimeException. (str "Invalid escape sequence "
                                                  (char-at input index)
                                                  " while reading string " buf))))))
          (recur (str buf ch) (inc index)))))))

(defmethod lexer/lex-impl :lexer/line-comment
  [_ input index]
  (loop [index (inc index)]
    (if (eof? input index)
      [[:token/eof] index]
      (case (char-at input index)
        \newline (lexer/lex-impl :lexer/default input (inc index))
        (recur (inc index))))))

(defmethod lexer/lex-impl :lexer/block-comment
  [_ input index]
  (loop [index (inc index)]
    (if (eof? input index)
      (throw (RuntimeException. (str "End of file while reading a block comment.")))
      (case (char-at input index)
        \} (lexer/lex-impl :lexer/default input (inc index))
        (recur (inc index))))))
