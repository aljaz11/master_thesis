module GlobalState
open Solidity
open FStar.String

(* 
    New type string_66 that only allows strings with 66 characters
    effectively simulating hexadecimal number of length 64 (+ '0x') == 256 bit number == 32 bytes
*)
type string_66 = s:string {length s = 66}   // another way to represent 32byte values

let default_string_66 : string_66 = 
    let def_str = "0x0000000000000000000000000000000000000000000000000000000000000000" in
    let _ = assume(String.length def_str = 66) in 
    def_str

(*
    Default address for roles
*)
let multiSigTreasury : address = to_address 0xaB23968d766D445BC9b370512d3085c345AcB235

(*
    Define creator address for msg.sender - address that has initialized the contract
    (Info from https://etherscan.io/address/0x3ac694ad2a9a616b6af4fc7e13ab08793eecaac7#code)
*)
let original_msg_sender : address = to_address 0x26c09DCd572Ec41dd55Ee099dB9a321E3B34b351


(*
Calculated keccak256("PAUSER_ROLE") from https://emn178.github.io/online-tools/keccak_256.html 
*)
let pauser_keccak : string_66 = 
    let def_str = "0x65d7a28e3265b37a6474929f336521b332c1681b933f6cb9f3376673440d862a" in 
    let _ = assume(String.length def_str = 66) in 
    def_str

(*
Calculated keccak256("MINTER_ROLE") from https://emn178.github.io/online-tools/keccak_256.html
*)
let minter_keccak : string_66 = 
    let def_str = "0x9f2df0fed2c77648de5860a4cc508cd0818c85b8b8a1ab4ceeef8d981c8956a6" in 
    let _ = assume(String.length def_str = 66) in 
    def_str

(*
Calculated keccak256("UPGRADER_ROLE") from https://emn178.github.io/online-tools/keccak_256.html 
*)
let upgrader_keccak : string_66 = 
    let def_str = "0x189ab7a9244df0848122154315af71fe140f3db0fe014031783b0946b8c9d2e3" in 
    let _ = assume(String.length def_str = 66) in 
    def_str

(*
Calculated keccak256("BRIDGE_OWNER_ROLE") from https://emn178.github.io/online-tools/keccak_256.html 
*)
let bridger_owner_keccak : string_66 = 
    let def_str = "0xca93eeebffcc91aeddd69986d2392810138feb62c9e4efc6996600ed00e90b6d" in 
    let _ = assume(String.length def_str = 66) in 
    def_str

(* 
    Relevant events:
        - event Reforged(address indexed account, uint256 amount, string indexed transaction);
        - event Transfer(address indexed from, address indexed to, uint256 value);
*)
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
    events_             : list event;

    (* mapping transaction string (transaction hash) to bool
       bool is by default set to `false` *)
    _transactions       : string_66 -> bool;

    (* type that contains all role hashes (keccak256 hashes) *)
    roles               : role;

    (* mapping role hashes (keccak256 hashes) into _RoleData struct *)
    _roles              : string_66 -> _RoleData;  

    (* uint that presents the total number of tokens in the existence
       essentially it presents all tokens that were ever minted *)
    _totalSupply        : uint;

    (* mapping address to uint (representing the balance of tokens for specific account) *)
    _balances           : address -> uint;

    (* address that receives transaction fees in native currency *)
    _bridgeOwner        : address;

    (* boolean variable, indicates if contract is paused *)
    _paused             : bool; 

    (* boolean variable, indicates if bridge is paused *)
    _bridgePaused       : bool;

    (* uint that presents the bridge transacion fee in native currency *)
    _minimumBridgeFee   : uint;

    (* mapping chain_id (uint) to the address of the specific token e.g., eEUR *)
    (* Example: maps Ethereum_chain to eEUR token *)
    _sameTokens         : uint -> address;

    (* uint that presents the minimal required amount for SendToChain *)
    _minimumSendToChainAmount   : uint;

    (* address of feeTresury *)
    _feeTreasury        : address;

    (* uint that presetns the bridge transaction fee percentage (10^6 == 1%) *)
    _bridgeFee          : uint;
}

let default_state : global_state = {
    events_         = [];
    _transactions   = ( fun x -> false );
    roles           = {
                        _PAUSER_ROLE        = pauser_keccak;        (* symulating keccak256("PAUSER_ROLE") *)
                        _MINTER_ROLE        = minter_keccak;        (* symulating keccak256("MINTER_ROLE") *)
                        _UPGRADER_ROLE      = upgrader_keccak;      (* symulating keccak256("UPGRADER_ROLE") *)
                        _BRIDGE_OWNER_ROLE  = bridger_owner_keccak; (* symulating keccak256("BRIDGE_OWNER_ROLE") *)
                        _ADMIN_eEUR         = default_string_66;    (* default 0x00 *)
    };
    (*_roles          = ( fun role -> { 
                                        members = ( fun addr -> false ); 
                                        adminRole = default_string_66 
                                    }); *)
    (* Add default account for reoles *)
    _roles          = ( fun role -> { 
                                        members = ( fun addr ->
                                                        if      (* role == _PAUSER_ROLE and addr = multiSigTreasury *)
                                                                (role = pauser_keccak  && addr = multiSigTreasury)
                                                                (* role == _MINTER_ROLE and addr = multiSigTreasury *)
                                                            ||  (role = minter_keccak  && addr = multiSigTreasury)
                                                                (* role == _UPGRADER_ROLE and addr = multiSigTreasury *)
                                                            ||  (role = upgrader_keccak && addr = multiSigTreasury)
                                                                (* role == _BRIDGE_OWNER_ROLE and addr = multiSigTreasury *)
                                                            ||  (role = bridger_owner_keccak && addr = multiSigTreasury)
                                                                (* role == _ADMIN_eEUR and addr = creator of the contract *)
                                                            ||  (role = default_string_66 && addr = original_msg_sender) 
                                                        then true
                                                        else false ); 
                                        adminRole = default_string_66 (* _ADMIN_eEUR  *)
                                    });
    _totalSupply    = Solidity.to_uint 0;
    _balances       = ( fun x -> Solidity.to_uint 0   );
    _bridgeOwner    = default_address;
    _paused         = false;
    _bridgePaused   = false;
    _minimumBridgeFee   = Solidity.to_uint 0;           
    _sameTokens     = ( fun x -> default_address );     // TODO
    // Ether_chain = 137 | eEUR (0x735fa792e731a2e8F83F32eb539841b7B72e6d8f) - https://etherscan.io/tx/0xc81b5f69aeda6eaa159f244d3aa5ae56a905c336b455f6dd37675937ef4f7c26 
    _minimumSendToChainAmount   = Solidity.to_uint 10000000000000000000000;   (* default value is 10^22 *)
    _feeTreasury    = multiSigTreasury;
    _bridgeFee      = Solidity.to_uint 300000; (* 300000 == 0.3% *)
}
