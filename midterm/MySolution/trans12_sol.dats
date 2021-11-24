(* ****** ****** *)
//
#include
"./../lambda2.dats"
//
(* ****** ****** *)
#dynload
"./../lambda1.dats"
(* ****** ****** *)
implement
main0() = ((*dummy*))
(* ****** ****** *)

typedef stamp = int

(* ****** ****** *)

local

assume
t2var_type =
ref@{
t2var_t1var= t1var
,
t2var_t1ype= t1ype
,
t2var_stamp= stamp
}

val
the_t2var_stamp =
ref_make_elt<stamp>(1)

fun
t2var_stamp_new
((*void*)): int =
let
val
stamp =
!the_t2var_stamp
in
!the_t2var_stamp := stamp+1; stamp
end // end of [t2var_stamp_new]

in

(* ****** ****** *)
implement
t2var_get_stamp
(X) = X->t2var_stamp
implement
t2var_get_t1ype
(X) = X->t2var_t1ype
(* ****** ****** *)

implement
t2var_new() =
ref@{
t2var_t1var= ""
,
t2var_t1ype= t1ype_new_ext()
,
t2var_stamp= t2var_stamp_new()
}

(* ****** ****** *)

implement
t2var_new_t1var
(name) =
let
val X = t2var_new()
in
  X->t2var_t1var := name; X
end

(* ****** ****** *)
implement
fprint_t2var(out, X) =
{
val () =
fprint!(out, X->t2var_t1var)
val () =
fprint!(out, "[", X->t2var_stamp, "]")
}
(* ****** ****** *)

end // end of [local]

(* ****** ****** *)
extern
fun
t1env_find
( t1env
, t1var): myoptn(t2var)
(* ****** ****** *)

implement
t1env_find
(env0, x0) = myoptn_nil()






datatype
t1env =
|
T1ENVnil of ()
|
T1ENVcons of
(t1var(*str*), t2var(*obj*), t1env)

(* ****** ****** *)

extern
fun
trans12(prgm: t1erm): t2erm
extern
fun
trans12_env
(prgm: t1erm, tenv: t1env): t2erm

(* ****** ****** *)

implement
trans12(prgm) =
trans12_env(prgm, T1ENVnil())

(* ****** ****** *)

extern
fun
t1env_find(t1env, t1var): myoptn(t2var)

(* ****** ****** *)
extern
fun
head(mylist(t1erm)): t1erm

implement
head(t1s)=
(
case+ t1s of
| mylist_nil()=>T1Mnil()
| mylist_cons(t1, t1s)=>t1
)

extern
fun
pop(mylist(t1erm)): mylist(t1erm)

implement
pop(t1s)=
(
case+ t1s of
| mylist_nil()=>mylist_nil()
| mylist_cons(t1, t1s)=>t1s
)



extern
fun
mylist_trans12(t1s: mylist(t1erm)): mylist(t2erm)

implement
mylist_trans12(t1s)=
(
let
val t2s= mylist_nil()
in
loop(t1s, t2s) where
{
fun
loop(t1s: mylist(t1erm), t2s: mylist(t2erm)): mylist(t2erm)=
(
if mylist_length(t1s) < 1 then t2s else
(
let
val head=head(t1s)
val head1=trans12(head)
val t3s=pop(t1s)
val t4s=mylist_cons(head1, t2s)
in
loop(t3s, t4s)
end
)
)
}
end
)

implement
trans12_env
(trm0, env0) =
(
case+ trm0 of
//
| T1Memp() => T2Memp()
| T1Mint(i0) => T2Mint(i0)
| T1Mbtf(b0) => T2Mbtf(b0)
| T1Mstr(s0) => T2Mstr(s0)
//
| T1Mvar(x1) =>
  T2Mvar(y1) where 
  { val-
    myoptn_cons(y1) = t1env_find(env0, x1) }
| T1Mlam(x1, T1, t2) =>
  let
    val y1 = t2var_new()
    val env1 = T1ENVcons(x1, y1, env0)
    val u2 = trans12_env(t2, env1)
  in
    T2Mlam(y1, T1, u2)
  end
| T1Mapp(t1,t2) =>
  let
    val u1 = trans12_env(t1, env0)
	val u2 = trans12_env(t2, env0)
  in
    T2Mapp(u1,u2)
  end
| T1Mlet(x1, t1, t2) =>
  let
    val y1 = t2var_new()
	val env1 = T1ENVcons(x1, y1, env0)
	val u1 = trans12_env(t1, env1)
	val u2 = trans12_env(t2, env1)
  in
    T2Mlet(y1, u1, u2)
  end
  
| T1Mopr(opr, t1s) =>
  let
    val t2s= mylist_trans12(t1s)
  in
    T2Mopr(opr, t2s)
  end
| T1Mifb(t1, t2, t3) =>
  let
    val u1 = trans12_env(t1, env0)
	val u2 = trans12_env(t2, env0)
	val u3 = trans12_env(t3, env0)
  in
    T2Mift(u1, u2, u3)
  end
| T1Mfix(x1, x2, T1, T2, t1) =>
  let
    val y1 = t2var_new()
	val env1 = T1ENVcons(x1, y1, env0)
	val y2 = t2var_new()
	val env2 = T1ENVcons(x2, y2, env1)
	val u1 = trans12_env(t1, env2)
  in
    T2Mfix(y1, y2, T1, T2, u1)
  end
| T1Mtup(t1,t2) =>
  let
    val u1=trans12_env(t1, env0)
    val u2=trans12_env(t2, env0)
  in
    T2Mtup(u1, u2)
  end
| T1Mfst(t1)=>
  let
    val u1= trans12_env(t1, env0)
  in
    T2Mfst(u1)
  end
| T1Msnd(t1)=>
  let
    val u1= trans12_env(t1, env0)
  in
    T2Msnd(u1)
  end
| T1Mann(t1, T1) =>
  let
    val u1= trans12_env(t1, env0)	
  in
    T2Mann(u1,T1)
  end
| T1Mnil() => T2Mnil()
| T1Mcons(t1,t2) =>
  let
    val u1= trans12_env(t1, env0)
	val u2= trans12_env(t2, env0)
  in
    T2Mcons(u1, u2)
  end
| T1Misnil(t1) =>
  let
    val u1= trans12_env(t1, env0)
  in
    T2Misnil(u1)
  end
| T1Mhead(t1) =>
  let
    val u1= trans12_env(t1, env0)
  in
    T2Mhead(u1)
  end
| T1Mtail(t1) =>
  let
    val u1= trans12_env(t1, env0)
  in
    T2Mtail(u1)
  end
| T1Mref_new(t1) =>
  let
    val u1= trans12_env(t1, env0)
  in
    T2Mref_new(u1)
  end
| T1Mref_get(t1) =>
  let
    val u1= trans12_env(t1, env0)
  in
    T2Mref_get(u1)
  end
| T1Mref_set(t1, t2) =>
  let
    val u1= trans12_env(t1, env0)
	val u2= trans12_env(t2, env0)
  in
    T2Mref_set(u1, u2)
  end
//

)
