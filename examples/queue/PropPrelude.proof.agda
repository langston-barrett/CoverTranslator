--#include "prelude.agda"
--#include "PropPrelude.agda"


proof_reverse_nil :: PropPrelude.prop_reverse_nil
  = ref@_ (reverse Unit Nil@_)

proof_append_nil_1 :: PropPrelude.prop_append_nil_1
  = ?

proof_append_nil_2 :: PropPrelude.prop_append_nil_2
  = \ (xs::List Unit) -> ref@_ (append Unit Nil@_ xs)