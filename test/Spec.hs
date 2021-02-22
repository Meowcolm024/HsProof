import           Control.Monad.Trans
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Logic
import           Proof
import           ProofRef
import           Types

-- | show the first goal
status :: Proof Prop
status = lift get >>= except . Right . head . _goal

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

statusTest :: Proof Prop
statusTest = do
    a    <- newProofObject (Atom "a")
    h    <- newProofObject (Atom "b" :-> Atom "c")
    goal <- newGoal (Atom "c")
    apply h
    status

doProof :: Proof Prop -> Either Result Prop
doProof p = evalState (runExceptT p) newPropRef

main :: IO ()
main = do
    print $ doProof simpleProof
    print $ doProof simpleProof'
    print $ doProof statusTest
