module MinHS.Evaluator where
import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Pretty
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import Debug.Trace
import Text.Show.Functions ()
import Data.Maybe (isJust, fromJust)
import MinHS.Env (addAll)


type VEnv = E.Env Value

data Value = I Integer
           | B Bool
           | Nil
           | Cons Integer Value
           -- Add other variants as needed
           | Closure VEnv Bind
           deriving (Show, Read, Eq)

instance PP.Pretty Value where
  pretty (I i) = numeric $ i
  pretty (B b) = datacon $ show b
  pretty (Nil) = datacon "Nil"
  pretty (Cons x v) = PP.parens (datacon "Cons" PP.<+> numeric x PP.<+> PP.pretty v)
  pretty _ = undefined -- how do you write pretty for Closure?

data SusExp = Sussy Exp | Evaluated Value deriving (Show) -- suspended expression
data SusComp = SusOp Op | SusCon | SusIf | SusBind Id | SusApp deriving (Show) -- suspended computation
data Frame = Frame SusComp [SusExp] deriving (Show) 
data FrameOrEnv = FoeF Frame | FoeE VEnv deriving (Show) 
type Stack = [FrameOrEnv] 
data MachineState = Evaluation Stack VEnv Exp | Return Stack VEnv Value deriving (Show)

-- do not change this definition
evaluate :: Program -> Value
evaluate [Bind _ _ _ e] = evalE e
evaluate _ = error "Input program did not have exactly one binding"

-- do not change this definition
evalE :: Exp -> Value
evalE expr = loop (msInitialState expr)
  where
    loop ms = -- (trace ("debug message " ++ show ms)) $  -- uncomment this line and pretty print the machine state/parts of it to
                                            -- observe the machine states
             if (msInFinalState newMsState)
                then msGetValue newMsState
                else loop newMsState
              where
                 newMsState = msStep ms

msInitialState :: Exp -> MachineState
msInitialState = Evaluation [] E.empty

-- checks whether machine is in final state
msInFinalState :: MachineState -> Bool
msInFinalState (Evaluation _ _ _) = False
msInFinalState (Return s e _) = null s -- && (e == E.empty)

-- returns the final value if machine is in final state. If the machine is not in final state, throw an error
msGetValue :: MachineState -> Value
msGetValue m = case m of
  Evaluation _ _ _ -> errorMsg
  Return _ _ v     -> if msInFinalState m then v else errorMsg
  where
    errorMsg = error "Value being asked when Machine isn't in Final State"

msStep :: MachineState -> MachineState
msStep m = case m of

  -- variables
  Evaluation s e (Var v) -> case (E.lookup e v) of
    Just val -> Return s e val
    Nothing -> error "Free variable found - Freedom is good, unless it is with variables"

  -- integers
  Evaluation s e (Num i) -> Return s e (I i)

  -- booleans
  Evaluation s e (Con "True") -> Return s e (B True)
  Evaluation s e (Con "False") -> Return s e (B False)
  -- Evaluation _ _ (Con _) -> error "You got Conned! Con was sent without 'True' or 'False'"

  -- primOps
  -- add
  Evaluation s e (App (App (Prim Add) x) y) -> Evaluation (FoeF (Frame (SusOp Add) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Add) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Add) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Add) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (I (i + j))

  -- subtract
  Evaluation s e (App (App (Prim Sub) x) y) -> Evaluation (FoeF (Frame (SusOp Sub) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Sub) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Sub) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Sub) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (I (i - j))

  -- multiply
  Evaluation s e (App (App (Prim Mul) x) y) -> Evaluation (FoeF (Frame (SusOp Mul) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Mul) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Mul) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Mul) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (I (i * j))

  -- quotient
  Evaluation s e (App (App (Prim Quot) x) y) -> Evaluation (FoeF (Frame (SusOp Quot) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Quot) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Quot) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Quot) [Evaluated (I i), Sussy y]) : s) e (I 0) -> error "BRUH, did you just try to divide by 0?"
  Return (FoeF (Frame (SusOp Quot) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (I (quot i j))

  -- remainder
  Evaluation s e (App (App (Prim Rem) x) y) -> Evaluation (FoeF (Frame (SusOp Rem) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Rem) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Rem) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Rem) [Evaluated (I i), Sussy y]) : s) e (I 0) -> error "BRUH, did you just try to divide (remainder) by 0?"
  Return (FoeF (Frame (SusOp Quot) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (I (rem i j))

  -- unary negation
  Evaluation s e (App (Prim Neg) x) -> Evaluation (FoeF (Frame (SusOp Neg) [Sussy x]) : s) e x
  Return (FoeF (Frame (SusOp Neg) [Sussy x]) : s) e (I i) -> Return s e (I (negate i))

  -- greater than
  Evaluation s e (App (App (Prim Gt) x) y) -> Evaluation (FoeF (Frame (SusOp Gt) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Gt) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Gt) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Gt) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (B (i > j))

  -- greater than or equal
  Evaluation s e (App (App (Prim Ge) x) y) -> Evaluation (FoeF (Frame (SusOp Ge) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Ge) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Ge) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Ge) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (B (i >= j))

  -- lesser than
  Evaluation s e (App (App (Prim Lt) x) y) -> Evaluation (FoeF (Frame (SusOp Lt) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Lt) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Lt) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Lt) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (B (i < j))

  -- lesser than or equal
  Evaluation s e (App (App (Prim Le) x) y) -> Evaluation (FoeF (Frame (SusOp Le) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Le) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Le) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Le) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (B (i <= j))

  -- equals
  Evaluation s e (App (App (Prim Eq) x) y) -> Evaluation (FoeF (Frame (SusOp Eq) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Eq) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Eq) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Eq) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (B (i == j))

  -- not equals
  Evaluation s e (App (App (Prim Ne) x) y) -> Evaluation (FoeF (Frame (SusOp Ne) [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame (SusOp Ne) [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame (SusOp Ne) [Evaluated (I i), Sussy y]) : s) e y
  Return (FoeF (Frame (SusOp Ne) [Evaluated (I i), Sussy y]) : s) e (I j) -> Return s e (B (i /= j))

  -- handing lists
  Evaluation s e (Con "Nil") -> Return [] e (valueConsedList (makeEvaluatedList (map takeEvaluatedOut s)))
  Evaluation s e (App (App (Con "Cons") x) y) -> Evaluation (FoeF (Frame SusCon [Sussy x, Sussy y]) : s) e x
  Return (FoeF (Frame SusCon [Sussy x, Sussy y]) : s) e (I i) -> Evaluation (FoeF (Frame SusCon [Evaluated (I i), Sussy y]) : s) e y

  -- primitive list ops
  Evaluation s e (App (Prim Head) (Con "Nil")) -> error "Head called on an empty list"
  Evaluation s e (App (Prim Head) (App (App (Con "Cons") x) y)) -> Evaluation s e x

  Evaluation s e (App (Prim Null) (Con "Nil")) -> Return s e (B True)
  Evaluation s e (App (Prim Null) _) -> Return s e (B False)

  Evaluation s e (App (Prim Tail) (Con "Nil")) -> error "Tail called on an empty list"
  Evaluation s e (App (Prim Tail) (App (App (Con "Cons") x) y)) -> Evaluation s e y

  -- if then else
  Evaluation s e (If x y z) -> Evaluation (FoeF (Frame SusIf [Sussy x, Sussy y, Sussy z]) : s) e x
  Return (FoeF (Frame SusIf [Sussy x, Sussy y, Sussy z]) : s) e (B True) -> Evaluation s e y
  Return (FoeF (Frame SusIf [Sussy x, Sussy y, Sussy z]) : s) e (B False) -> Evaluation s e z

  -- let
  Evaluation s e (Let [Bind x _ [] y] expr) -> Evaluation (FoeF (Frame (SusBind x) [Sussy y, Sussy expr]) : s) e y
  Return (FoeF (Frame (SusBind x) [Sussy y, Sussy expr]) : s) e v -> Evaluation s (addAll e [(x, v)]) expr

  -- functions evaluate to closures
  Evaluation s e (Recfun b) -> Return s e (Closure e b)

  -- function application changes the environment and pushes the older environment to the stack
  Evaluation s e (App expr1 expr2) -> Evaluation (FoeF (Frame SusApp [Sussy expr1, Sussy expr2]) : s) e expr1
  Return (FoeF (Frame SusApp [Sussy expr1, Sussy expr2]) : s) e c@(Closure ce cb) -> Evaluation (FoeF (Frame SusApp [Evaluated c, Sussy expr2]) : s) e expr2
  Return (FoeF (Frame SusApp [Evaluated c@(Closure ce (Bind _ _ _ expr)), Sussy expr2]) : s) e v -> Evaluation (FoeE e : s) (updated e c v) expr

  Return (FoeE se : s) e v -> Return s se v
  _ -> error "Ruh-roh!"


-- helper functions for handling lists
takeEvaluatedOut :: FrameOrEnv -> Maybe Integer
takeEvaluatedOut (FoeF (Frame SusCon (Evaluated (I i) : _))) = Just i
takeEvaluatedOut _ = Nothing

makeEvaluatedList :: [Maybe Integer] -> [Integer]
makeEvaluatedList = foldr (\a b -> if isJust a then fromJust a : b else b) []

valueConsedList :: [Integer] -> Value
valueConsedList xs = foldr Cons Nil (reverse xs)

-- helper functions for handling function application
updated :: VEnv -> Value -> Value -> VEnv
updated e c@(Closure _ (Bind i _ [] _)) v2 = addAll e [(i, c)]
updated e c@(Closure _ (Bind i _ (x:_) _)) v2 = addAll e [(i, c), (x, v2)]
updated e _ _ = e