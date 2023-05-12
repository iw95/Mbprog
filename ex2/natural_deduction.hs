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
_ = case (readMaybe "FOVar \"aa\"") :: Maybe FOTerm of 
        Nothing     -> "parse error"; 
        Just x      -> "fine, we\'ve got " ++ show x
-- Defining a custom instance of Show for nicer input format is wellcome

-- Custom "show" for printing it pretty. 
instance Show FOTerm where
    show (FOVar x)          = x
    show (FOFun f [])       = f
    show (FOFun f (x : xs)) = 
        f ++ "(" ++ show x ++ foldr ((++) . (", "++) . show) ")" xs

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
    deriving (Read, Eq)

instance Show FOFormula where
    show (FOPred f []) = f
    show (FOPred f (x:xs)) = 
        f ++ "(" ++ show x ++ foldr ((++) . (", "++) . show) ")" xs
    show Top = "Top"
    show Bot = "Bot"
    show (Conj a b) = "Conj " ++ (show a) ++ " " ++ (show b)
    show (Disj a b) = "Disj " ++ (show a) ++ " " ++ (show b)
    show (Impl a b) = "Impl " ++ (show a) ++ " " ++ (show b)
    show (All x form) = "All " ++ x ++ ". " ++ (show form)
    show (Exi x form) = "Exi " ++ x ++ ". " ++ (show form)


data FOJudgement = FOJudgement [VarName] [FOFormula] FOFormula
    deriving (Show, Eq)


unique :: [VarName] -> [VarName]
unique = foldr (\ x t -> if elem x t then t else x:t) []

t1 = unique ["a", "a", "b" , "a"] == [ "b", "a"]

-- Free variables of a term
termFreeVars :: FOTerm -> [VarName]
termFreeVars (FOVar name) = [name]
termFreeVars (FOFun name termList) 
    = unique (concat (map termFreeVars termList))

t20 = termFreeVars (FOVar "x") == ["x"]
t21 = termFreeVars (FOFun "plus" [FOVar "x", FOFun "zero" []]) == ["x"]
t22 = termFreeVars (FOFun "plus" [FOFun "succ" [FOFun "zero" []], FOFun "zero" []]) == []

-- Free variables of a formula
formFreeVars :: FOFormula -> [VarName]
formFreeVars (FOPred name termList) 
    = unique (concat (map termFreeVars termList))
formFreeVars Top = []
formFreeVars Bot = []
formFreeVars (Conj f1 f2) = unique ((formFreeVars f1) ++ (formFreeVars f2))
formFreeVars (Disj f1 f2) = unique ((formFreeVars f1) ++ (formFreeVars f2))
formFreeVars (Impl f1 f2) = unique ((formFreeVars f1) ++ (formFreeVars f2))
formFreeVars (All name f) = delete name (formFreeVars f)
formFreeVars (Exi name f) = delete name (formFreeVars f)
-- relplace with your code

t30 = formFreeVars (All "x" (FOPred "equal" [FOVar "x", FOVar "x"])) == []
t31 = formFreeVars (All "x" (FOPred "equal" [FOVar "x", FOVar "y"])) == ["y"]


-- funSubst t x s implements t[s/x] for terms
funSubst :: FOTerm -> VarName -> FOTerm -> FOTerm
funSubst (FOVar name) varName substTerm = 
    if name == varName then substTerm else (FOVar name)
funSubst (FOFun name termList) varName substTerm =
    FOFun 
        name 
        (map (\ term -> funSubst term varName substTerm) termList)
    -- relplace with your code

t40 = funSubst (FOVar "x") "x" (FOVar "y") == FOVar "y"
t41 = funSubst (FOVar "x") "x" (FOFun "plus" [FOVar "x", FOFun "zero" []]) == FOFun "plus" [FOVar "x", FOFun "zero" []]
t42 = funSubst (FOFun "plus" [FOVar "x", FOFun "zero" []]) "x" (FOFun "plus" [FOVar "x", FOFun "zero" []]) == FOFun "plus" [ FOFun "plus" [FOVar "x", FOFun "zero" []] , FOFun "zero" []]


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
formSubst form@(All name f) var term = 
    if name == var
        then All name f
        else All newname (formSubst (formSubst f name (FOVar newname)) var term)
           where newname = rename form term
formSubst form@(Exi name f) var term = 
    if name == var 
        then Exi name f
        else Exi newname (formSubst (formSubst f name (FOVar newname)) var term)
           where newname = rename form term

t50 = formSubst (FOPred "isNat" [FOVar "x"]) "x" (FOFun "zero" []) == FOPred "isNat" [FOFun "zero" []]
t51 = formSubst (Exi "x" (FOPred "isNat" [FOVar "x"])) "x" (FOFun "zero" []) == Exi "x" (FOPred "isNat" [FOVar "x"])
-- here is sth. wrong
-- all free variables of the substTerm must be renamed, 
-- if they intersect with the orig formula and cause captures


-- rename form term finds a new variable name that is not in the free variables of that formula and term
rename ::  FOFormula -> FOTerm -> VarName
rename form term = head (filter (\ var -> not (elem var freeV)) genVarNames)
    where freeV = unique ((formFreeVars form) ++ (termFreeVars term))

t60 = True -- tbc.


genVarNames :: [String]
genVarNames = [reverse (c : s) | s <- "" : genVarNames, c <- ['a'..'z']]
-- replace with your code 

t70 = True -- tbc.


type ProofState = [FOJudgement]


hyp :: FOJudgement -> Maybe ProofState
hyp (FOJudgement _ gamma phi) = 
   if (elem phi gamma) then Just [] else Nothing

f1 = FOPred "equals" [FOVar "x", FOVar "y"]
j1 = (FOJudgement [] [f1] f1)
tt010 = hyp j1 == Just []
j2 = (FOJudgement [] [] f1)
tt011 = hyp j2 == Nothing


andI :: FOJudgement -> Maybe ProofState
andI (FOJudgement sigma gamma (Conj phi psi)) 
    = Just [ FOJudgement sigma gamma phi ,
             FOJudgement sigma gamma psi ]
andI _ = Nothing

fA = FOPred "A" []
fB = FOPred "B" []
conjAB = Conj fA fB
j3 = FOJudgement [] [] conjAB
j3A = FOJudgement [] [] fA
j3B = FOJudgement [] [] fB

tt020 = andI j3 == Just [ j3A, j3B ]

andE1 :: FOJudgement -> FOFormula -> Maybe ProofState
andE1 (FOJudgement sigma gamma phi) psi 
    = Just [FOJudgement sigma gamma (Conj phi psi)]

tt030 = andE1 j3A fB == Just [j3]

andE2 :: FOJudgement -> FOFormula -> Maybe ProofState
andE2 (FOJudgement sigma gamma psi) phi 
    = Just [FOJudgement sigma gamma (Conj phi psi)]

tt040 = andE2 j3B fA == Just [j3]

orI1 :: FOJudgement -> Maybe ProofState
orI1 (FOJudgement sigma gamma (Disj phi psi)) 
    = Just [(FOJudgement sigma gamma phi)]
orI1 _ = Nothing

disjAB = (Disj fA fB)
j4 = FOJudgement [] [] disjAB
tt050 = orI1 j4 == Just [j3A]

orI2 :: FOJudgement -> Maybe ProofState
orI2 (FOJudgement sigma gamma (Disj phi psi)) 
    = Just [(FOJudgement sigma gamma psi)]
orI2 _ = Nothing

tt060 = orI2 j4 == Just [j3B]

orE :: FOJudgement -> FOFormula -> Maybe ProofState
orE (FOJudgement sigma gamma xi) (Disj phi psi)
    = Just [ FOJudgement sigma gamma (Disj phi psi) ,
             FOJudgement sigma (phi : gamma) xi ,
             FOJudgement sigma (psi : gamma) xi  ]
orE _ _ = Nothing
-- uniquness gamma ????

j5 = FOJudgement [] [fA] conjAB
j6 = FOJudgement [] [fB] conjAB
tt070 = orE j3 disjAB == Just [ j4 , j5, j6 ]

implI :: FOJudgement -> Maybe ProofState
implI (FOJudgement sigma gamma (Impl phi psi))
    = Just [ FOJudgement sigma (phi : gamma) psi ]
implI _ = Nothing

implF_A_B = Impl fA fB
implJ_o_o_Impl_A_B = FOJudgement [] [] implF_A_B
implJ_o_A_B = FOJudgement [] [fA] fB
tt080 = implI implJ_o_o_Impl_A_B == Just [ implJ_o_A_B ]

implE :: FOJudgement -> FOFormula -> Maybe ProofState
implE (FOJudgement sigma gamma psi) phi
    = Just [ FOJudgement sigma gamma (Impl phi psi) ,
             FOJudgement sigma gamma phi  ]

implJ_o_o_B = FOJudgement [] [] fB
implJ_o_o_A = FOJudgement [] [] fA
tt090 = implE implJ_o_o_B fA == Just [ implJ_o_o_Impl_A_B, implJ_o_o_A ]

sublist :: Eq a => [a] -> [a] -> Bool
sublist l1 l2 = foldr (\ x b -> ((elem x l2) && b) ) True l1

tt100 = sublist [1,2,3] [1,3,4] == False

allI :: FOJudgement -> Maybe ProofState
allI (FOJudgement sigma gamma (All name phi))
    = Just [ FOJudgement (name:sigma) gamma phi ]
allI _ = Nothing

allF_x_A = All "x" fA
allJ_o_o_All_x_A = FOJudgement [] [] allF_x_A
allJ_x_o_A = FOJudgement ["x"] [] fA
tt110 = allI allJ_o_o_All_x_A == Just [ allJ_x_o_A ]

allE :: FOJudgement -> FOFormula -> FOTerm -> Maybe ProofState
allE (FOJudgement sigma gamma phi') (All name phi) term
    = if (formSubst phi name term == phi') && 
         (sublist (termFreeVars term) sigma) 
         then Just [ FOJudgement sigma gamma (All name phi) ]
         else Nothing
allE _ _ _ = Nothing

allF_x_eqlXX = All "x" (FOPred "Equals" [ FOVar "x" , FOVar "x" ])
eql00 = FOPred "Equals" [ FOFun "zero" [] , FOFun "zero" [] ]
j_o_o_eql00 = FOJudgement [] [] eql00
j_o_o_Alleql00 = FOJudgement [] [] allF_x_eqlXX
tt120 = allE j_o_o_eql00 allF_x_eqlXX (FOFun "zero" []) == Just [ j_o_o_Alleql00 ]

exI :: FOJudgement -> FOTerm -> Maybe ProofState
exI (FOJudgement sigma gamma (Exi name phi)) term
    = if (sublist (termFreeVars term) sigma) 
        then Just [ FOJudgement sigma gamma (formSubst phi name term) ]
        else Nothing
exI _ _ = Nothing

fPred_isNat_x = FOPred "isNat" [FOVar "x"]
fExi_isNat_x = Exi "x" fPred_isNat_x
exIj_o_o_exiIsNatX = FOJudgement [] [] fExi_isNat_x
j_o_o_isNat_zero = FOJudgement [] [] (FOPred "isNat" [FOFun "zero" []])
tt130 = exI exIj_o_o_exiIsNatX (FOFun "zero" []) == Just [ j_o_o_isNat_zero ]

exE :: FOJudgement -> FOFormula -> Maybe ProofState
exE (FOJudgement sigma gamma psi) (Exi name phi)
    = if elem name sigma
        then Nothing
        else Just [ FOJudgement sigma gamma (Exi name phi) ,
                    FOJudgement (name : sigma) (phi : gamma) psi ]
exE _ _ = Nothing
-- what about free variables here ?

j_o_o_isNat_x = FOJudgement [] [] fPred_isNat_x
j_x_o_isNat_x = FOJudgement ["x"] [ fPred_isNat_x ] fPred_isNat_x
tt140 = exE j_o_o_isNat_x fExi_isNat_x 
    == Just [ exIj_o_o_exiIsNatX, j_x_o_isNat_x ]



botE :: FOJudgement -> Maybe ProofState
botE (FOJudgement sigma gamma phi)
    = Just [ FOJudgement sigma gamma Bot ]
topI :: FOJudgement -> Maybe ProofState
topI (FOJudgement sigma gamma Top)
    = Just []
topI _ = Nothing




-- Initialize proof state with the goal
initPS :: FOJudgement -> ProofState
initPS = undefined           -- replace with your code

-- Main code
proofStep :: (String, ProofState) -> (String, ProofState)
proofStep = undefined        -- replace with your code

-- Interactive shell wrapper
statefulInteract :: ((String, a) -> (String, a)) -> (String, a) -> IO ()
statefulInteract f (s , x) = 
    putStr s 
    >> getLine 
    >>= (return . \s -> (f (s , x))) 
    >>= statefulInteract f

{-
ioHandling :: (String, ProofState, Int) -> (String, ProofState, Int)
ioHandling (s, p, n) =
    ("proving " ++ show (head pnew), pnew, nnew)
    where (snew, pnew, nnew) = proofStep (s, p)


ruleDispatch :: String -> ProofState -> Maybe ProofState
ruleDispatch 
"andE1" p = 
    putStr "please enter the right formule: " >> getLine
    >>= readMaybe 
    >>= \x -> case x of
        Nothing -> "failed"
        Just x -> andE1 (head p) x
-}



-- Test for statefulInteract
siTest :: (String, Int) -> (String, Int)
siTest (s , n) = 
    ("[" ++ show n ++ "] your input is: " ++ show s ++ "\n[" 
         ++ show (n + 1) ++ "] enter another string: ", n + 1)

parseFOTerm s = 
    case (readMaybe s) :: Maybe FOTerm of 
        Nothing     -> "parse error"; 
        Just x      -> "fine, we\'ve got " ++ show x

{-
parseFOTerm "FOFun \"x\" [FOVar \"x\"]"
parseFOTerm "FOFun \"x\" [FOFun \"x\" []]"
-}

parseFOFormula s = 
    case (readMaybe s) :: Maybe FOFormula of 
        Nothing     -> "parse error"; 
        Just x      -> show x


goals = [
      undefined :: FOJudgement   -- first test formula 
    , undefined :: FOJudgement   -- second test formula
    , undefined :: FOJudgement   -- third test formula, etc
 ]

prove n = statefulInteract proofStep ("We are proving " ++ show (goals !! n) ++ ". Which rule to apply?> ", initPS $ goals !! n)



{-
proof:

[] [] |-- Top 
- topI - 
Success 


[] [] |-- All x. Impl (P x) (P x) 
- allI -
[x] [] |-- Impl (P x) (P x)
- implI -
[x] [P x] |-- (P x)
- hyp -
Success


[] 
[   Impl (All x. H(x)) => M(x),
    H(s) ]
|-- M(s)
-------------------- implE H(s) ---------------------------

GoalStack 1.
(TopGoal)
[] 
[   Impl (All x. H(x)) => M(x),
    H(s) ]
|-- H(s)
---------------------- hyp ---------------------------------
Success


GoalStack 2.
(TopGoal)
[] 
[   Impl (All x. H(x)) => M(x),
    H(s) ]
|-- Impl H(s) M(s)
--------------------- allE s ------------------------------
[] 
[   Impl (All x. H(x)) => M(x),
    H(s) ]
|-- All newName. Impl H(newName) M(newName)
---------------------- hyp ---------------------------------
Success


-}
