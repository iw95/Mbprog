import Data.Char
import Text.Read
import Data.List


-- Some aliases
type VarName  = String
type FunName  = String
type PredName = String

-- Data type of first-order terms
data FOTerm 
    = FOVar VarName 
    | FOFun FunName [FOTerm]
    deriving (Read, Eq, Ord)
-- We make it an instance of the Read class, which can be used as follows: 
_ = case (readMaybe "FOVar \"aa\"") :: Maybe FOTerm of Nothing -> "parse error"; Just x -> "fine, we\'ve got " ++ show x
-- Defining a custom instance of Show for nicer input format is wellcome

-- Custom "show" for printing it pretty. 
instance Show FOTerm where
    show (FOVar x)          = x
    show (FOFun f [])       = f
    show (FOFun f (x : xs)) = f ++ "(" ++ show x ++ foldr ((++) . (", "++) . show) ")" xs

-- Data type of first-order formulas
data FOFormula 
    = FOPred PredName [FOTerm]
    | Top
    | Bot
    | Conj FOFormula FOFormula
    | Disj FOFormula FOFormula
    | Impl FOFormula FOFormula
    | All VarName FOFormula
    | Exi VarName FOFormula
    -- add more clauses
    deriving (Read, Show)


data FOJudgement = FOJudgement [VarName] [FOFormula] FOFormula
    deriving (Show)


unique :: [VarName] -> [VarName]
unique [] = []
unique (h : r) = if elem h r then unique r else h : (unique r)

-- Free variables of a term
termFreeVars :: FOTerm -> [VarName]
termFreeVars (FOVar name) = [name]
termFreeVars (FOFun name termList) 
    = unique (concat (map termFreeVars termList))

-- Free variables of a formula
formFreeVars :: FOFormula -> [VarName]
formFreeVars (FOPred name termList) 
    = unique (concat (map termFreeVars termList))
formFreeVars Top = []
formFreeVars Bot = []
formFreeVars (Conj f1 f2) = (formFreeVars f1) ++ (formFreeVars f2)
formFreeVars (Disj f1 f2) = (formFreeVars f1) ++ (formFreeVars f2)
formFreeVars (Impl f1 f2) = (formFreeVars f1) ++ (formFreeVars f2)
formFreeVars (All name f) = delete name (formFreeVars f)
formFreeVars (Exi name f) = delete name (formFreeVars f)
-- relplace with your code

-- funSubst t x s implements t[s/x] for terms
funSubst :: FOTerm -> VarName -> FOTerm -> FOTerm
funSubst (FOVar name) varName substTerm = 
    if name == varName then substTerm else (FOVar name)
funSubst (FOFun name termList) varName substTerm =
    FOFun 
        name 
        (map (\ term -> funSubst term varName substTerm) termList)
    -- relplace with your code



-- formSubst t x s implements t[s/x] for formulas
formSubst :: FOFormula -> VarName -> FOTerm -> FOFormula
formSubst (FOPred name termList) var term
    = FOPred name (map (\ t -> funSubst t var term) termList)
formSubst Top _ _ = Top
formSubst Bot _ _ = Bot
formSubst (Conj f1 f2) var term = 
    Conj (formSubst f1 var term) (formSubst f2 var term)
formSubst (Disj f1 f2) var term = 
    Disj (formSubst f1 var term) (formSubst f2 var term)
formSubst (Impl f1 f2) var term = 
    Impl (formSubst f1 var term) (formSubst f2 var term)
formSubst (All name f) var term = 
    if name == var 
        then formSubst (rename f name) var term
        else formSubst f var term
formSubst (Exi name f) var term = 
    if name == var 
        then formSubst (rename f name) var term
        else formSubst f var term

-- replace with your code 



data ProofState = ProofState -- replace with your code

-- Initialize proof state with the goal
initPS :: FOJudgement -> ProofState
initPS = undefined           -- replace with your code

-- Main code
proofStep :: (String, ProofState) -> (String, ProofState)
proofStep = undefined        -- replace with your code

-- Interactive shell wrapper
statefulInteract :: ((String, a) -> (String, a)) -> (String, a) -> IO ()
statefulInteract f (s , x) = putStr s >> getLine >>= (return . \s -> f (s , x)) >>= statefulInteract f

-- Test for statefulInteract
siTest :: (String, Int) -> (String, Int)
siTest (s , n) = ("[" ++ show n ++ "] your input is: " ++ show s ++ "\n[" ++ show (n + 1) ++ "] enter enother string: ", n + 1)

goals = [
      undefined :: FOJudgement   -- first test formula 
    , undefined :: FOJudgement   -- second test formula
    , undefined :: FOJudgement   -- third test formula, etc
 ]

prove n = statefulInteract proofStep ("We are proving " ++ show (goals !! n) ++ ". Which rule to apply?> ", initPS $ goals !! n)
