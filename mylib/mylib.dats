(* ****** ****** *)

datatype
myoptn(a:t@ype) =
| myoptn_nil of ()
| myoptn_cons of (a)

(* ****** ****** *)

datatype
mylist(a:t@ype) =
| mylist_nil of ()
| mylist_cons of (a, mylist(a))

(* ****** ****** *)

extern
fun
{a:t@ype}
mylist_sing(x0: a): mylist(a)

(* ****** ****** *)

extern
fun
{a:t@ype}
mylist_length(xs: mylist(a)): int

(* ****** ****** *)
extern
fun
{a:t@ype}
mylist_append
(xs: mylist(a), ys: mylist(a)): mylist(a)
(* ****** ****** *)

extern
fun
{a:t@ype}
mylist_reverse(xs: mylist(a)): mylist(a)
extern
fun
{a:t@ype}
mylist_rappend
(xs: mylist(a), ys: mylist(a)): mylist(a)

(* ****** ****** *)

extern
fun
{a:t@ype}
mylist_remove
(xs: mylist(a), x0: a): mylist(a)

(* ****** ****** *)
(*
HX-2021-10-05:
Implementation should be given below
*)
(* ****** ****** *)

implement
{a}
mylist_sing(x0) =
mylist_cons(x0, mylist_nil())

(* ****** ****** *)

implement
{a}
mylist_length(xs) =
loop(xs, 0) where
{
fun
loop(xs: mylist(a), r0: int): int =
case+ xs of
| mylist_nil() => r0
| mylist_cons(x1, xs) => loop(xs, r0+1)
}

(* ****** ****** *)

implement
{a}
mylist_append(xs, ys) =
mylist_rappend<a>
(mylist_reverse<a>(xs), ys)

(* ****** ****** *)

implement
{a}
mylist_reverse(xs) =
mylist_rappend<a>(xs, mylist_nil())

(* ****** ****** *)

implement
{a}
mylist_rappend(xs, ys) =
case+ xs of
|
mylist_nil() => ys
|
mylist_cons(x1, xs) =>
mylist_rappend<a>(xs, mylist_cons(x1, ys))

(* ****** ****** *)

(* end of [mylib.dats] *)
