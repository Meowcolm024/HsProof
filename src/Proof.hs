module Proof where

import           Control.Monad.Trans
import           Control.Monad.Trans.Except     ( except )
import           Control.Monad.Trans.State
import           ProofRef
import           Types

qed :: Proof Prop
qed = do
    ref <- lift get
    except $ case _goal ref of
        []      -> Left Proved
        (x : _) -> Left (Failed x)

apply' :: Appliable a => a -> Proof ()
apply' p = do
    ref <- lift get
    case app p . head . _goal $ ref of
        Left  Proved     -> finishGoal
        Left  (Failed p) -> except $ Left (Failed p)
        Right p          -> mutGoal 0 p

apply :: ObjectId -> Proof ()
apply i = apply' =<< getProofObject i
