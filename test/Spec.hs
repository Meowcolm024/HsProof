import           Control.Monad.Trans
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Logic
import           Proof
import           ProofRef
import           Types

-- | show the first goal
status :: Proof PropRef
status = lift get >>= except . Right

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
example :: Proof PropRef
example = do
    p    <- newProofObject (Not (Atom "q"))
    h    <- newProofObject (Atom "p" :-> Atom "q")
    g    <- newProofObject (Not (Atom "p") :-> (Atom "r" :/\ Atom "s"))
    goal <- newGoal (Atom "r")
    contrapostive `applyTo'` h
    applyM' imply [h, p] h
    applyM' imply [g, h] g
    disjunctionL `applyTo'` g
    apply g
    qed

doProof :: Proof a -> Either Result a
doProof p = evalState (runExceptT p) newPropRef

main :: IO ()
main = do
    print $ doProof simpleProof
    print $ doProof simpleProof'
    print $ doProof statusTest
    print $ doProof exfTest
    print $ doProof example
