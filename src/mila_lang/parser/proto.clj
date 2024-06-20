(ns mila-lang.parser.proto)

(defrecord CArg [name type])
(defrecord CArithmAdd [lhs rhs])
(defrecord CArithmDiv [lhs rhs])
(defrecord CArithmMod [lhs rhs])
(defrecord CArithmMul [lhs rhs])
(defrecord CArithmSub [lhs rhs])
(defrecord CArithmUnNeg [val])
(defrecord CArrayType [from to type])
(defrecord CAssignment [lhs rhs])
(defrecord CBeginEndBlock [blocks])
(defrecord CBoolean [value])
(defrecord CBreak [])
(defrecord CCall [target args])
(defrecord CCmpEq [lhs rhs])
(defrecord CCmpGt [lhs rhs])
(defrecord CCmpGe [lhs rhs])
(defrecord CCmpLt [lhs rhs])
(defrecord CCmpLe [lhs rhs])
(defrecord CCmpNe [lhs rhs])
(defrecord CConst [lhs rhs])
(defrecord CContinue [])
(defrecord CDowntoFor [iter-var iter-var-init iter-var-end body])
(defrecord CExit [])
(defrecord CFloat [value])
(defrecord CFunction [name arglist return-type locals body forward])
(defrecord CIfElse [cond then else])
(defrecord CIndexAssignment [arr index-expr rhs])
(defrecord CIndexOp [arr-name index-expr])
(defrecord CInteger [value])
(defrecord CLogAnd [lhs rhs])
(defrecord CLogOr [lhs rhs])
(defrecord CProcedure [name arglist locals body forward])
(defrecord CProgram [program-name program-blocks main-block])
(defrecord CString [value])
(defrecord CSymbol [value])
(defrecord CToFor [iter-var iter-var-init iter-var-end body])
(defrecord CVarDecl [vars type])
(defrecord CWhile [cond body])
