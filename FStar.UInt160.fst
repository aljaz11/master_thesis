/// For FStar.UIntN.fstp: anything that you fix/update here should be
/// reflected in [FStar.IntN.fstp], which is mostly a copy-paste of
/// this module.
///
/// Except, as compared to [FStar.IntN.fstp], here:
///  - every occurrence of [int_t] has been replaced with [uint_t]
///  - every occurrence of [@%] has been replaced with [%].
///  - some functions (e.g., add_underspec, etc.) are only defined here, not on signed integers

/// This module provides an abstract type for machine integers of a
/// given signedness and width. The interface is designed to be safe
/// with respect to arithmetic underflow and overflow.

/// Note, we have attempted several times to re-design this module to
/// make it more amenable to normalization and to impose less overhead
/// on the SMT solver when reasoning about machine integer
/// arithmetic. The following github issue reports on the current
/// status of that work.
///
/// https://github.com/FStarLang/FStar/issues/1757
module FStar.UInt160
open FStar.UInt
open FStar.Mul

let n = 160

type t : eqtype =
  | Mk: v:uint_t n -> t

#set-options "--max_fuel 0 --max_ifuel 0"

(** A coercion that projects a bounded mathematical integer from a
    machine integer *)
val v (x:t) : Tot (uint_t n)
let v x = x.v

(** A coercion that injects a bounded mathematical integers into a
    machine integer *)
val uint_to_t (x:uint_t n) : Pure t
  (requires True)
  (ensures (fun y -> v y = x))

irreducible
let uint_to_t x = Mk x


(** Injection/projection inverse *)
val uv_inv (x : t) : Lemma
  (ensures (uint_to_t (v x) == x))
  [SMTPat (v x)]

let uv_inv _ = ()

(** Projection/injection inverse *)
val vu_inv (x : uint_t n) : Lemma
  (ensures (v (uint_to_t x) == x))
  [SMTPat (uint_to_t x)]
let vu_inv _ = ()

(** An alternate form of the injectivity of the [v] projection *)
val v_inj (x1 x2: t): Lemma
  (requires (v x1 == v x2))
  (ensures (x1 == x2))
let v_inj _ _ = ()

(** Constants 0 and 1 *)
val zero : x:t{v x = 0}
let zero = uint_to_t 0


(**** Addition primitives *)

(** Bounds-respecting addition

    The precondition enforces that the sum does not overflow,
    expressing the bound as an addition on mathematical integers *)
val add (a:t) (b:t) : Pure t
  (requires (size (v a + v b) n))
  (ensures (fun c -> v a + v b = v c))
let add a b = Mk (add (v a) (v b))

(** Underspecified, possibly overflowing addition:

    The postcondition only enures that the result is the sum of the
    arguments in case there is no overflow *)
val add_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a + v b) n ==> v a + v b = v c))
let add_underspec a b = Mk (add_underspec (v a) (v b))

(** Addition modulo [2^n]

    Machine integers can always be added, but the postcondition is now
    in terms of addition modulo [2^n] on mathematical integers *)
val add_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.add_mod (v a) (v b) = v c))
let add_mod a b = Mk (add_mod (v a) (v b))

(**** Subtraction primitives *)


(** Bounds-respecting subtraction

    The precondition enforces that the difference does not underflow,
    expressing the bound as a difference on mathematical integers *)
val sub (a:t) (b:t) : Pure t
  (requires (size (v a - v b) n))
  (ensures (fun c -> v a - v b = v c))
let sub a b = Mk (sub (v a) (v b))

(** Underspecified, possibly overflowing subtraction:

    The postcondition only enures that the result is the difference of
    the arguments in case there is no underflow *)
val sub_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a - v b) n ==> v a - v b = v c))
let sub_underspec a b = Mk (sub_underspec (v a) (v b))

(** Subtraction modulo [2^n]

    Machine integers can always be subtractd, but the postcondition is
    now in terms of subtraction modulo [2^n] on mathematical integers *)
val sub_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.sub_mod (v a) (v b) = v c))
let sub_mod a b = Mk (sub_mod (v a) (v b))

(**** Multiplication primitives *)


(** Bounds-respecting multiplication

    The precondition enforces that the product does not overflow,
    expressing the bound as a product on mathematical integers *)
val mul (a:t) (b:t) : Pure t
  (requires (size (v a * v b) n))
  (ensures (fun c -> v a * v b = v c))
let mul a b = Mk (mul (v a) (v b))

(** Underspecified, possibly overflowing product

    The postcondition only enures that the result is the product of
    the arguments in case there is no overflow *)
val mul_underspec (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c ->
    size (v a * v b) n ==> v a * v b = v c))
let mul_underspec a b = Mk (mul_underspec (v a) (v b))

(** Multiplication modulo [2^n]

    Machine integers can always be multiplied, but the postcondition
    is now in terms of product modulo [2^n] on mathematical integers *)
val mul_mod (a:t) (b:t) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mul_mod (v a) (v b) = v c))
let mul_mod a b = Mk (mul_mod (v a) (v b))

(**** Modulo primitives *)

(** Euclidean remainder

    The result is the modulus of [a] with respect to a non-zero [b] *)
val rem (a:t) (b:t{v b <> 0}) : Pure t
  (requires True)
  (ensures (fun c -> FStar.UInt.mod (v a) (v b) = v c))
let rem a b = Mk (mod (v a) (v b))

(**** Bitwise operators *)

/// Also see FStar.BV

(** Bitwise logical conjunction *)
val logand (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logand` v y = v z))
let logand x y = Mk (logand (v x) (v y))

(** Bitwise logical exclusive-or *)
val logxor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logxor` v y == v z))
let logxor x y = Mk (logxor (v x) (v y))

(** Bitwise logical disjunction *)
val logor (x:t) (y:t) : Pure t
  (requires True)
  (ensures (fun z -> v x `logor` v y == v z))
let logor x y = Mk (logor (v x) (v y))

(** Bitwise logical negation *)
val lognot (x:t) : Pure t
  (requires True)
  (ensures (fun z -> lognot (v x) == v z))
let lognot x = Mk (lognot (v x))

(**** Shift operators *)

(** Shift right with zero fill, shifting at most the integer width *)
val shift_right (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_right (v a) (UInt32.v s) = v c))
let shift_right a s = Mk (shift_right (v a) (UInt32.v s))

#push-options "--z3rlimit 80 --fuel 1"  //AR: working around the interleaving semantics of pragmas
(** Shift left with zero fill, shifting at most the integer width *)
val shift_left (a:t) (s:UInt32.t) : Pure t
  (requires (UInt32.v s < n))
  (ensures (fun c -> FStar.UInt.shift_left (v a) (UInt32.v s) = v c))
let shift_left a s = Mk (shift_left (v a) (UInt32.v s))

(**** Comparison operators *)

(** Equality

    Note, it is safe to also use the polymorphic decidable equality
    operator [=] *)
let eq (a:t) (b:t) : Tot bool = eq #n (v a) (v b)

(** Greater than *)
let gt (a:t) (b:t) : Tot bool = gt #n (v a) (v b)

(** Greater than or equal *)
let gte (a:t) (b:t) : Tot bool = gte #n (v a) (v b)

(** Less than *)
let lt (a:t) (b:t) : Tot bool = lt #n (v a) (v b)

(** Less than or equal *)
let lte (a:t) (b:t) : Tot bool = lte #n (v a) (v b)


#pop-options

(*** Infix notations *)
unfold let op_Plus_Hat = add
unfold let op_Plus_Question_Hat = add_underspec
unfold let op_Plus_Percent_Hat = add_mod
unfold let op_Subtraction_Hat = sub
unfold let op_Subtraction_Question_Hat = sub_underspec
unfold let op_Subtraction_Percent_Hat = sub_mod
unfold let op_Star_Hat = mul
unfold let op_Star_Question_Hat = mul_underspec
unfold let op_Star_Percent_Hat = mul_mod
unfold let op_Percent_Hat = rem
unfold let op_Hat_Hat = logxor
unfold let op_Amp_Hat = logand
unfold let op_Bar_Hat = logor
unfold let op_Less_Less_Hat = shift_left
unfold let op_Greater_Greater_Hat = shift_right
unfold let op_Equals_Hat = eq
unfold let op_Greater_Hat = gt
unfold let op_Greater_Equals_Hat = gte
unfold let op_Less_Hat = lt
unfold let op_Less_Equals_Hat = lte

(**** To input / output constants *)
(** In decimal representation *)
val to_string: t -> Tot string
let to_string _ = admit ()

(** In hex representation (with leading 0x) *)
val to_string_hex: t -> Tot string
let to_string_hex _ = admit ()

(** In fixed-width hex representation (left-padded with zeroes, no leading 0x) *)
val to_string_hex_pad: t -> Tot string
let to_string_hex_pad _ = admit ()

val of_string: string -> Tot t
let of_string _ = admit ()

#set-options "--lax"
//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verification check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __uint_to_t (x:int) : Tot t
    = uint_to_t x
#reset-options