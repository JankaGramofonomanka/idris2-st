module Control.ST.ImplicitCall

import Control.ST

-- TODO no ide if this has any value
||| Make 'call' implicit.
||| This makes ST programs less verbose, at the cost of making error messages
||| potentially more difficult to read.
--export implicit
imp_call
   : STrans m t ys ys'
  -> {auto res_prf : SubRes ys xs}
  -> STrans m t xs (\res => updateWith (ys' res) xs res_prf)
imp_call = call
