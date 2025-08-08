module WFST

let _spost a s =
  s0:s -> pre:Type0 -> 
    (a -> s -> post:Type0{post ==> pre})

let spost_monotonic #a #s (sp:(_spost a s)) : Type0 = 
  forall s0 pre pre' r s1. 
    (pre ==> pre') ==> (sp s0 pre r s1 ==> sp s0 pre' r s1)
let spost a s = sp:(_spost a s){spost_monotonic sp}

let spost_ord (sp sp':spost 'a 's) : Type0 =
  forall s0 pre r s1. sp s0 pre r s1 ==> sp' s0 pre r s1

let ret #a #s (x:a) : spost a s =
  let sp : _spost a s = fun s0 pre r s1 -> pre /\ x == r /\ s0 == s1 in
  assert (spost_monotonic sp);
  sp

let (let!) #a #b #s (sp:spost a s) (f:a -> spost b s) : spost b s =
  let sp : _spost b s = fun s0 pre r2 s2 ->
    exists r1 s1. f r1 s1 (sp s0 pre r1 s1) r2 s2 
  in
  assert (spost_monotonic sp);
  sp

let get #s () : spost s s =
  let sp : _spost s s =
    fun s0 pre r s1 -> pre /\ r == s0 /\ s1 == s0
  in assert (spost_monotonic sp);
  sp

let put #s (s':s) : spost unit s =
  let sp : _spost unit s =
    fun _ pre _ s1 -> pre /\ s1 == s'
  in assert (spost_monotonic sp);
  sp

let incorrect #a #s
  (presumes : s -> Type0)
  (achieves : a -> s -> Type0)
  (sp:spost a s) : Type0 =
  forall r (s1:s).
    achieves r s1 ==> exists s0. sp s0 (presumes s0) r s1 /\ presumes s0

let is_even (x:int) : bool =
  x % 2 = 0

let example_3_1 : spost unit (int * int * int) =
  let! (x,y,z) = get () in
  if is_even x then
    if not (is_even y) then put (x, y, 42)
    else ret ()
  else ret () 

(** Cezar: Fails! Manual proof needed to instantiate the existentials. Similar to what we did in Rocq **)
let _ =
  assert (
      incorrect 
        (fun (x,y,z) -> z = 11) 
        (fun _ (x,y,z) -> z = 42 /\ is_even x /\ not (is_even y))
        example_3_1)
