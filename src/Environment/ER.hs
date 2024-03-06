module Environment.ER where

import Environment.ERWS

import qualified Control.Monad.Reader as Reader

newtype ER e r a = ER { run :: a }
  -- ER { coER :: Reader.Reader (Environment ER e r)  }
