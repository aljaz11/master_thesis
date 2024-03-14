module Statements

open Solidity

(*
        Statement01: Overflow in `_mint` function is not possible in the `unchecked` part (of soliditxy code)
        
        Proof is trivial, since we have alerady shown that 
        updated_totalSupply >= updated_balances[account] `assertion (_totalSupply >= updated _balances[account])`, and 
        that increase of _totalSupply didn't result in overflow `overflow_check and match`,
        thus it logically implies that _accountBalance_upd has not overlowed!
*)
let lemma_overflow_impossible (_totalSupply_upd:uint) (_accountBalance_upd:uint) : Lemma 
                                        (requires   ((FStar.UInt256.lte _totalSupply_upd Solidity.max_uint) /\
                                                     (FStar.UInt256.gte _totalSupply_upd _accountBalance_upd)))
                                        (ensures  (FStar.UInt256.lte _accountBalance_upd Solidity.max_uint)) 
                                        = ()

(*	    Statement01: Global state reamins valid after refogrge *)
// TODO

(*	    Statement02: After the reforge execution account 
        `to`'s balance is increased for exactly `amount`
*)
// TODO

(*	    Statement03: After the reforge execution account 
        `msg.sender`'s balance is decreased for exactly `amount` (+ `fee`)
*)
//TODO 

(*	    Statement04: Reentrancy attack is not possible in reforge 
*)
// TODO
