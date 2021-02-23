module HsProof.ProofRef where

import           Control.Lens
import           Control.Monad.Trans
import           Control.Monad.Trans.State
import           HsProof.Types

newProof l p = lift $ do
    ref <- get
    put $ ref & l %~ (++ [p])
    return $ ref ^. object & length

newProofObject :: Prop -> Proof ObjectId
newProofObject = newProof object

newGoal :: Prop -> Proof ObjectId
newGoal = newProof goal

mutProof l i p = lift $ do
    ref <- get
    put $ ref & l . ix i .~ p

mutProofObject :: ObjectId -> Prop -> Proof ()
mutProofObject = mutProof object

mutGoal :: ObjectId -> Prop -> Proof ()
mutGoal = mutProof goal

finishGoal :: Proof ()
finishGoal = lift $ do
    ref <- get
    put $ ref & goal .~ tail (ref ^. goal)

getProofObject :: ObjectId -> Proof Prop
getProofObject i = lift $ do
    ref <- get
    return $ (ref ^. object) ^?! ix i

newPropRef :: PropRef
newPropRef = PropRef [] []
