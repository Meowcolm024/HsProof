import           Control.Monad.Trans
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.State
import           Logic
import           Proof
import           Types

apply' :: Prop -> Proof (Either Prop Prop)
apply' p = lift $ do
    ref <- get
    return $ if p == head (_goal ref) then Right None else Left p

qed :: Prop -> Proof Prop
qed p = except $ if p == None then Left Proved else Left (Failed p)

status :: Proof Prop
status = do
    ref <- lift get
    except . Right . head . _goal $ ref

simpleProof :: Proof Prop
simpleProof = do
    a    <- newProofObject (Atom "b")
    goal <- newGoal (Atom "a")
    -- status
    r    <- apply' =<< getProofObject a
    qed $ case r of
        Right b -> b
        Left  b -> b

main :: IO ()
main = print $ evalState (runExceptT simpleProof) newPropRef
