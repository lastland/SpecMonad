# STEx context

Parent: [Code](../CONTEXT.md). [Examples.v](Examples.v) defines deterministic
state/exception programs in ExtLib stateT; [STEx.v](STEx.v) supplies forward
specifications and verification rules.

STEx maps initial state and propositional pre to propositions over `E + A * S`
implying pre, without monotonicity. Exceptions are inl and have no final state;
normal returns are inr. Return/bind/get/put/raise/catch supply operations, but
monad laws remain unproved. Bind propagates errors; catch runs the handler at
the original state with the error proposition as precondition.

obsSTEx combines runStateT equality with pre. Verify requires specification
to imply observation, like Reader and opposite to ST. Verify_ret/bind/get/put/
raise support mst; no catch verification theorem is supplied.
Incorrect requires an initial-state witness for each asserted outcome;
IncorrectNormal/Err restrict to each branch and Incorrect' conjoins them.
Verify transfers these witnesses to computation outcomes.

ReadIfIncWrite connects its specification to Examples.read_if_inc_write:
increment at initial state at least 42, exception otherwise.
Exists_in_obs_less witnesses error, not final state; Exists_in_obs_more
witnesses normal final states above 42. Read computation → carrier/observation
→ judgments. Both files use ExtLib/arithmetic; STEx.v also CoqHammer.
Neither imports Common/Taxonomy; Common/IOStateExc's sum tags are reversed.
