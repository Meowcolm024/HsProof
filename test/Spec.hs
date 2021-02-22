import           Control.Monad.Trans
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Proof
import           ProofRef
import           Types

status :: Proof Prop
status = lift get >>= except . Right . head . _goal

simpleProof :: Proof Prop
simpleProof = do
    a    <- newProofObject (Atom "a")
    h    <- newProofObject (Atom "a" :-> Atom "b")
    goal <- newGoal (Atom "b")
    apply h
    apply a
    -- status
    qed

main :: IO ()
main = print $ evalState (runExceptT simpleProof) newPropRef
