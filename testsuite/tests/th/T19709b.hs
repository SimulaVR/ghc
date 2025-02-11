{-# LANGUAGE TemplateHaskell, ExplicitForAll, PolyKinds, TypeApplications #-}

module T19709b where

import GHC.Exts
import Language.Haskell.TH

$( let levfun :: forall (r :: RuntimeRep) (a :: TYPE r). a -> ()
       levfun = error "e1"  -- NB: this, so far, is OK: no levity-polymorphic binder

   in levfun (error @Any "e2")  -- but this is very naughty: levity-polymorphic argument
      `seq` return [] )
