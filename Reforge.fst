module Reforge

open Solidity
open FStar.Preorder
open FStar.All
open FStar.String

(* 
    New type string_66 that only allows strings with 66 characters
    effectively simulating hexadecimal number of length 64 (+ '0x') == 256 bit number
*)
type string_66 = s:string {length s = 66}   // another way to represent 32byte values

val make_string_66 : s:string -> Tot (option string_66)
let make_string_66 s =
  if String.length s = 66 then Some s else None

val default_string_66 : string_66
let default_string_66 = 
  match make_string_66 "0x0000000000000000000000000000000000000000000000000000000000000000" with
  | Some s -> s
  | _ -> failwith "failed"

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
    // list of events
    events_         : list event;

    // mapping transaction string (transaction hash) to bool
    // bool is by default set to `false`
    _transactions   : string_66 -> bool;

    // type that contains all role hashes (keccak256 hashes)
    roles           : role;

    // mapping role hashes (keccak256 hashes) into _RoleData struct
    _roles          : string_66 -> _RoleData;  

    // uint that presents the total number of tokens in the existence
    // essentially it presents all tokens that were ever minted
    _totalSupply    : uint;

    // mapping address to uint (representing the balance of tokens for specific account)
    _balances       : address -> uint;

    // address that receives transaction fees in native currency
    _bridgeOwner    : address;

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
    _bridgeOwner   = default_address;
}

// function that checks if specific account has specific role assgined to them
// from `eEUR_AccessControlUpgredeable.sol`
let hasRole     (state: global_state)
                (input_role: string_66)
                (account: address)
                : bool =
     Solidity.get (Solidity.get state._roles input_role).members account  
     // returns bool from mapping => `return _roles[role].members[account];`    


let _mint   (state: global_state)
            (account: address)
            (amount: uint)
            : ML (option (unit) * global_state) =
        let s : ref global_state = alloc state in
            try 
                // i) check that `account` is not zero address (default address)
                let check_address = (FStar.UInt160.eq account default_address) in
                if check_address then 
                    // if address is zero address raise an exception
                    (raise Solidity.SolidityZeroAddress; ())
                else();

                // ii) increase the total supply with add_mod -> thus overflow is not possible
                s := {!s with _totalSupply = FStar.UInt256.add_mod (!s)._totalSupply amount};

                // iii) increase the account's balance by amount without checking it
                // TODO currently it uses add_mod, but it should somehow use only add!
                s :=    {!s with _balances = Solidity.set (!s)._balances account 
                            (FStar.UInt256.add_mod 
                                (Solidity.get (!s)._balances account) 
                                amount
                            )
                        };

                // return updated state
                (Some(), !s)
            with 
            // if any other error occurs keep the old state
            _ -> (None, state)

let reforge     (state: global_state) 
                (in_msg: msg)
                (to: address)
                (amount: uint)
                (fee: uint)
                (rate: string)  (* Exchange rate *)
                (sourceChainId: uint)
                (transaction: string_66)
                : ML (option (unit) * global_state) =
    let s : ref global_state = alloc state in 
        try 
            // i)   check if account has correct role permission
            let check_requirement_1 = (hasRole (!s) (!s).roles._BRIDGE_OWNER_ROLE (in_msg).sender) in
            let check_requirement_2 = (hasRole (!s) (!s).roles._MINTER_ROLE (in_msg).sender) in 
            if not (check_requirement_1 && check_requirement_2) then 
                (raise Solidity.SolidityInsufficientRole; ())
            else ();
            
            // ii)   check if requirement is satisfied (transaction has not been initialized yet)
            let check_requirement_3 = Solidity.get (!s)._transactions transaction in 
            if check_requirement_3 then 
                // if it is `true` then we need to raise an exception
                (raise Solidity.SolidityTransactionAlreadyProcessed; ())
            else ();

            // iii) mint `amount` of tokens to account `to`
            let (ret__, st__) = _mint (!s) to amount in 
                match ret__ with 
                    | Some _ -> ( 
                                    // updated state with minted amount
                                    s:= st__; 

                                    // check if fee is not zero (greater than 0)
                                    let check_fee_not_zero = FStar.UInt256.gt fee (Solidity.to_uint 0) in 
                                    if check_fee_not_zero then
                                        (
                                        // iv) mint `fee` to `_bridgeOwner`
                                        let (ret__2, st__2) = _mint (!s) (!s)._bridgeOwner fee in 
                                            match ret__2 with 
                                                | Some _ -> (
                                                            // updated state with bridgeOwner fee
                                                            s:= st__2; 

                                                            // v)  set transaciton to true
                                                            s := {!s with _transactions = Solidity.set 
                                                                                          (!s)._transactions transaction true };

                                                            // vi)  update state with the new event - emit Reforged(to, amount, transaction);
                                                            s := {!s with events_ = Reforged to amount transaction :: (!s).events_};

                                                            // return updated state
                                                            (Some (), !s))

                                                | _ -> raise Solidity.SolidityMintError
                                        )
                                    else (

                                        // v)  set transaciton to true
                                        s := {!s with _transactions = Solidity.set (!s)._transactions transaction true };

                                        // vi)  update state with the new event - emit Reforged(to, amount, transaction);
                                        s := {!s with events_ = Reforged to amount transaction :: (!s).events_};

                                        // return updated state
                                        (Some (), !s)
                                    )
                                )

                    | _     -> raise Solidity.SolidityMintError

            
        with
            // if any other error occurs keep the old state
            _ -> (None, state)