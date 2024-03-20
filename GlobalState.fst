module GlobalState
open Solidity
open FStar.String

(* 
    New type string_66 that only allows strings with 66 characters
    effectively simulating hexadecimal number of length 64 (+ '0x') == 256 bit number
*)
type string_66 = s:string {length s = 66}   // another way to represent 32byte values

let default_string_66 : string_66 = 
    let def_str = "0x0000000000000000000000000000000000000000000000000000000000000000" in
    let _ = assume(String.length def_str = 66) in 
    def_str
// Add relevant event for reforge
// event Reforged(address indexed account, uint256 amount, string indexed transaction);
// event Transfer(address indexed from, address indexed to, uint256 value);
type event = 
    | Reforged : address -> uint -> string_66 -> event
    | Transfer : address -> address -> uint -> event

(*
Add all possible roles (they have type string_66 since keccak256 returns hash - hex number of lenght 64)
*)
(*
type role =  
	| PAUSER_ROLE        : string_66 -> role
	| MINTER_ROLE        : string_66 -> role
	| UPGRADER_ROLE      : string_66 -> role
	| BRIDGE_OWNER_ROLE  : string_66 -> role
    | ADMIN_eEUR         : string_66 -> role
*)
type role = { 
	_PAUSER_ROLE        : string_66;
	_MINTER_ROLE        : string_66;
	_UPGRADER_ROLE      : string_66; 
	_BRIDGE_OWNER_ROLE  : string_66;
    _ADMIN_eEUR         : string_66;
}

(*
Struct from `eEUR_AccessControlUpgreadable.sol` that defines if specific address 
has assigned specific role (`true`) 
*)
noeq type _RoleData = {
    members     : address -> bool;
    adminRole   : string_66
}

noeq type global_state = {
    (* list of events *)
    events_         : list event;

    (* mapping transaction string (transaction hash) to bool
       bool is by default set to `false` *)
    _transactions   : string_66 -> bool;

    (* type that contains all role hashes (keccak256 hashes) *)
    roles           : role;

    (* mapping role hashes (keccak256 hashes) into _RoleData struct *)
    _roles          : string_66 -> _RoleData;  

    (* uint that presents the total number of tokens in the existence
       essentially it presents all tokens that were ever minted *)
    _totalSupply    : uint;

    (* mapping address to uint (representing the balance of tokens for specific account) *)
    _balances       : address -> uint;

    (* address that receives transaction fees in native currency *)
    _bridgeOwner    : address;

    (* boolean variable, indicates if contract is paused *)
    _paused         : bool; 

}

let default_state : global_state = {
    events_         = [];
    _transactions   = ( fun x -> false );
    roles           = {
                        _PAUSER_ROLE        = default_string_66;
                        _MINTER_ROLE        = default_string_66;
                        _UPGRADER_ROLE      = default_string_66;
                        _BRIDGE_OWNER_ROLE  = default_string_66;
                        _ADMIN_eEUR         = default_string_66;
    };
    _roles          = ( fun role -> { 
                                        members = ( fun addr -> false ); 
                                        adminRole = default_string_66 
                                    });    
    _totalSupply    = Solidity.to_uint 0;
    _balances       = ( fun x -> Solidity.to_uint 0   );
    _bridgeOwner    = default_address;
    _paused         = false;
}
