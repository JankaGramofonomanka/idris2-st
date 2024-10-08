module Control.ST.Exception

import Control.ST
--import Control.Catchable
--import Control.IOExcept

public export
interface Exception (0 m : Type -> Type) errorType | m where
  throw : errorType -> STrans m a ctxt (const ctxt)

  catch
     :               STrans m a in_res  (const out_res)
    -> (errorType -> STrans m a out_res (const out_res))
    ->               STrans m a in_res  (const out_res)

export
implementation Exception (Either errorType) errorType where
  throw err = lift (Left err)
  catch prog f = do
    res <- runAs prog
    case res of
      Left err => f err
      Right ok => pure ok

export
implementation Exception Maybe () where
  throw err = lift Nothing
  catch prog f = do
    res <- runAs prog
    case res of
      Nothing => f ()
      Just ok => pure ok

-- TODO Ignoring for now
{-
export
implementation Exception (IOExcept errorType) errorType where
  throw err = lift (ioe_fail err)
  catch prog f = do
    io_res <- runAs prog
    res <- lift $ catch (do r <- io_res; pure (Right r)) (pure . Left)
    either (\err => f err) (\ok => pure ok) res
-}
