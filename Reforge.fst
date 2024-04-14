module Reforge

open Solidity
open FStar.Preorder
open FStar.All
open FStar.String
open Statements
open GlobalState
open CommonFunctions
open FStar.List

(*  function that mints `amount` of tokens to `account` *)
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
                    raise Solidity.SolidityZeroAddress
                else();

                // ii) check that contract is not paused (mimic of _beforeTokenTransfer hook)
                let hook_check = paused (!s) in 
                if not hook_check then 
                    // if contract is paused
                    raise Solidity.SolidityPaused
                else();

                // iii) increase the total supply with add_mod -> check if this results in overflow
                let _totalSupply = (!s)._totalSupply in 
                let _accountBalance = (Solidity.get (!s)._balances) account in 
                (*  Assume that _totalSupply contains all the tokens thus specific account balance is at
                    most _totalSupply
                *)
                let _ = assume (FStar.UInt256.gte _totalSupply _accountBalance) in 
                match overflow_check (!s)._totalSupply amount with 
                    | Some res -> (
                                    s := {!s with _totalSupply = res};

                                    (*  iv) increase the account's balance 
                                        by amount without checking it (normal add), since 
                                        it cannot result in overflow -> ** we 
                                        assume (know) that there is at most 
                                        _totalSupply tokens ** 
                                    *)
                                    s :=    {!s with _balances = Solidity.set (!s)._balances account 
                                                (FStar.UInt256.add
                                                    (Solidity.get (!s)._balances account) 
                                                    amount
                                                )
                                            };
                                    (*
                                        Verify that updated _totalSupply >= updated _balances[account]
                                    *)
                                    let _totalSupply_upd = (!s)._totalSupply in 
                                    let _accountBalance_upd = (Solidity.get (!s)._balances) account in
                                    let _ = assert (FStar.UInt256.gte _totalSupply_upd _accountBalance_upd) in
                                    
                                    (*
                                        Verify that overlof cannot happen using lemma
                                    *)
                                    let _ = Statements.lemma_overflow_impossible  _totalSupply_upd _accountBalance in 

                                    (*
                                        Verify that the updated `_accountBalance` has increased exactly for `amount`
                                    *)
                                    let _ = assert (FStar.UInt256.eq (FStar.UInt256.add _accountBalance amount) _accountBalance_upd) in

                                    (*
                                       Update state with the new event - emit Transfer(address(0), account, amount);                                                            
                                    *)
                                    let events_length_old = length (!s).events_ in 
                                    s := {!s with events_ = Transfer Solidity.default_address account amount :: (!s).events_};

                                    // verify that the events_ list has grown - event has been emitted
                                    let events_length_new = length (!s).events_ in 
                                    let _ = assert(events_length_old < events_length_new) in 

                // return updated state
                (Some(), !s))
                    | _ -> (raise Solidity.SolidityOverflow)
                
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
        // Apply default state
        s := default_state;
        try 
            // i)   check if account has correct role permission
            let check_requirement_1 = (hasRole (!s) (!s).roles._BRIDGE_OWNER_ROLE (in_msg).sender) in
            let check_requirement_2 = (hasRole (!s) (!s).roles._MINTER_ROLE (in_msg).sender) in 
            if not (check_requirement_1 && check_requirement_2) then 
                raise Solidity.SolidityInsufficientRole
            else ();

            // Verify that account must have either of the two roles (BRIDGE_OWNER_ROLE or MINTER_ROLE)
            let _ = assert(check_requirement_1 || check_requirement_2) in 
            
            // ii)   check if requirement is satisfied (transaction has not been initialized yet)
            let check_requirement_3 = Solidity.get (!s)._transactions transaction in 
            if check_requirement_3 then 
                // if it is `true` then we need to raise an exception
                raise Solidity.SolidityTransactionAlreadyProcessed
            else ();

            // verify that each transaciton can be issued only once
            let _ = assert(not check_requirement_3) in 

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

                                        // Verify that fee is always greater than 0 (semi-definite number)
                                        let _ = assert(FStar.UInt256.gt fee (Solidity.to_uint 0)) in

                                        // iv) mint `fee` to `_bridgeOwner`
                                        let (ret__2, st__2) = _mint (!s) (!s)._bridgeOwner fee in 
                                            match ret__2 with 
                                                | Some _ -> (
                                                            // updated state with bridgeOwner fee
                                                            s:= st__2; 

                                                            // v)  set transaciton to true
                                                            s := {!s with _transactions = Solidity.set 
                                                                                          (!s)._transactions transaction true };

                                                            let events_length_old = length (!s).events_ in 

                                                            // vi)  update state with the new event - emit Reforged(to, amount, transaction);
                                                            s := {!s with events_ = Reforged to amount transaction :: (!s).events_};

                                                            // verify that the events_ list has grown - event has been emitted
                                                            let events_length_new = length (!s).events_ in 
                                                            let _ = assert(events_length_old < events_length_new) in 

                                                            // return updated state
                                                            (Some (), !s))

                                                | _ -> raise Solidity.SolidityMintError
                                        )
                                    else (

                                        // v)  set transaciton to true
                                        s := {!s with _transactions = Solidity.set (!s)._transactions transaction true };

                                        let events_length_old = length (!s).events_ in 

                                        // vi)  update state with the new event - emit Reforged(to, amount, transaction);
                                        s := {!s with events_ = Reforged to amount transaction :: (!s).events_};

                                        // verify that the events_ list has grown - event has been emitted
                                        let events_length_new = length (!s).events_ in 
                                        let _ = assert(events_length_old < events_length_new) in 

                                        // return updated state
                                        (Some (), !s)
                                    ) 
                                )

                    | _     -> raise Solidity.SolidityMintError


        with
            // if any other error occurs keep the old state
            _ -> (None, state)