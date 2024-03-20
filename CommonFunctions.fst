module CommonFunctions

open Solidity
open GlobalState

(* function that checks if specific account has specific role assgined to them
   from `eEUR_AccessControlUpgredeable.sol` *)
let hasRole     (state: global_state)
                (input_role: string_66)
                (account: address)
                : bool =
     Solidity.get (Solidity.get state._roles input_role).members account  
     // returns bool from mapping => `return _roles[role].members[account];`   

(*  function returns current value of global variable `_paused`  *)
let paused      (state: global_state)
                : bool =
                state._paused

(*  check if addition of two uints results in overflow
    e.g., in _mint => x = _totalSupply and y = amount
 *)
let overflow_check (x:uint) (y:uint) : option uint =
    // checks if (uint_max - x) < y ==> overflow
    if UInt256.lt (UInt256.sub Solidity.max_uint x) y then None 
    else Some (UInt256.add x y) // overflow not possible!