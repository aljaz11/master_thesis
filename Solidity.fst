module Solidity
// This is derived with the help of the:
     // Project-everest/ethereum-star: https://github.com/project-everest/ethereum-star
     // And https://github.com/mrsmkl/eth-fstar/blob/master/Token.fst 

open FStar.All
open FStar.ST
open FStar.UInt
open FStar.Heap
open FStar.UInt160
open FStar.UInt256
open FStar.Int
open FStar.List 
open FStar.Map

(*   Define basic types and their basics methods  *)
type uint = FStar.UInt256.t
type int256 = FStar.Int.int_t 256

val to_uint: int -> Tot uint
let to_uint n = FStar.UInt256.uint_to_t (FStar.UInt.to_uint_t 256 n) 

val to_int256: int -> Tot int256
let to_int256 n = FStar.Int.to_int_t 256 n

// Addresses are 20 bytes long == 160 bits
type address:eqtype = FStar.UInt160.t

val to_address: int -> Tot address
let to_address n = FStar.UInt160.uint_to_t (FStar.UInt.to_uint_t 160 n)

(*   Default values for data types  *)
val default_address : address
let default_address = to_address 0

val default_uint256 : uint
let default_uint256 = to_uint 0 

val default_int256 : int256 
let default_int256 = to_int256 0



(*
     Defined list operations
*)
let rec length #a (l:list a)
     : nat 
     = match l with 
          | [] -> 0
          | _ :: tl -> 1 + length tl

val list_length : #a:Type -> list a -> uint
let list_length #a lst = to_uint (Solidity.length lst)


val list_nth : #a:Type -> list a -> uint -> ML a
let list_nth #a lst n = List.nth lst (UInt256.v n)

val list_set : #a:Type -> list a -> uint -> a -> ML (list a)
let list_set #a lst n elem =
  let n = UInt256.v n in
  List.mapi (fun i a -> if i = n then elem else a) lst 


// mapping is already implemented in FStar.Map module
// as well as `sel` and `upd`
type mapping = FStar.Map.t

type msg = {
     value : uint;
     sender: address;
}

assume val getMessage: unit -> ST msg
       (requires (fun h -> true))
       (ensures (fun h x h' -> h == h'))

type block = {
     number : uint;
}

assume val getBlock: unit -> ST block
       (requires (fun h -> true))
       (ensures (fun h x h' -> h == h'))

exception SolidityThrow
exception SolidityReturn
exception SolidityBadReturn
exception SolidityTransactionAlreadyProcessed
exception SolidityInsufficientRole
exception SolidityZeroAddress
exception SolidityMintError

(*    
     Implementation of updating of map (set), it takes old mapping, key and value, 
     and returns the updated mapping, or if keys are the same just "old" value.
     Essentailly it is used to update the value associated with specific key.
     Taken from: https://github.com/mrsmkl/eth-fstar/blob/master/Token.fst 
*)
val set : #key:eqtype -> #vl:Type -> (key -> vl) -> key -> vl -> (key -> vl)
let set #key #vl f ind x ind2 = if ind = ind2 then x else f ind2

(*
     Get's value associated with key from mapping
     Taken from: https://github.com/mrsmkl/eth-fstar/blob/master/Token.fst
*)
val get : #key:eqtype -> #vl:Type -> (key -> vl) -> key -> vl
let get #key #vl f ind = f ind
