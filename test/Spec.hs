import           Control.Monad                  ( (>=>) )
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Logic
import           Proof
import           ProofRef
import           Types

-- | proof a -> (a -> ~b) -> (~c -> b) -> c
simpleProof :: Proof Prop
simpleProof = do
    a    <- newProofObject (Atom "a")
    h    <- newProofObject (Atom "a" :-> Not (Atom "b"))
    p    <- newProofObject (Not (Atom "c") :-> Atom "b")
    goal <- newGoal (Atom "c")
    contrapostive `applyTo'` p
    eliminateDN `applyTo'` p
    apply p
    apply h
    apply a
    qed

simpleProof' :: Proof Prop
simpleProof' = do
    a    <- newProofObject (Atom "a")
    h    <- newProofObject (Atom "a" :-> Atom "b")
    h'   <- newProofObject (Atom "a" :-> Atom "a")
    goal <- newGoal (Atom "b")
    apply h'
    apply h
    apply a
    abort

statusTest :: Proof PropRef
statusTest = do
    a    <- newProofObject (Atom "a")
    h    <- newProofObject (Atom "b" :-> Atom "c")
    goal <- newGoal (Atom "c")
    apply h
    status

-- | exf
exfTest :: Proof Prop
exfTest = do
    a    <- newProofObject (Atom "a")
    b    <- newProofObject (Not (Atom "a"))
    d    <- conjunction `applyToM` [a, b]
    goal <- newGoal (Atom "c")
    let theorem p@(x :/\ Not y) = if x == y then Right F else Left $ Failed p
    theorem `applyTo'` d
    exfalso d
    qed

-- | q -> (q -> ~q) -> (~p -> r /\ s) -> r
exampleTheorem :: Prop
exampleTheorem =
    Not (Atom "q")
        :-> (Atom "p" :-> Atom "q")
        :-> (Not (Atom "p") :-> (Atom "r" :/\ Atom "s"))
        :-> Atom "r"

proofExample :: ProofResult PropRef
proofExample = proof exampleTheorem $ do
    a <- intro      -- ~q
    h <- intro      -- p -> q
    g <- intro      -- ~p -> (r /\ s)
    contrapostive `applyTo'` h
    (h >$> g) >>= (`applyTo'` a)
    disjunctionL `applyTo'` a
    apply a
    qed

doProof :: Proof a -> Either Result a
doProof p = evalState (runExceptT p) newPropRef

showResult :: Show a => ProofResult a -> String
showResult (Left  Proved    ) = "Q.E.D."
showResult (Left  (Failed p)) = "Proof failed with " ++ show p
showResult (Right p         ) = show p

printResult :: Show a => ProofResult a -> IO ()
printResult = putStrLn . showResult

main :: IO ()
main = do
    printResult $ doProof simpleProof
    printResult $ doProof simpleProof'
    printResult $ doProof statusTest
    printResult $ doProof exfTest
    printResult $ proofExample
