module SendToChain

open FStar.All
open Solidity
open GlobalState
open CommonFunctions

(* function _transfer *)
let _transfer 	(state:global_state)
				(from:address)
				(to:address)
				(amount:uint)
				: ML (option (unit) * global_state) =
    let s : ref global_state = alloc state in
		try 
			(* i) check that `from` is not zero address (default address) *)
					let check_from = (FStar.UInt160.eq from default_address) in
					if check_from then 
						// if address is zero address raise an exception
						raise Solidity.SolidityZeroAddress
					else();
			
			 (* ii) check that `to` is not zero address (default address) *)
					let check_to = (FStar.UInt160.eq to default_address) in
					if check_to then 
						// if address is zero address raise an exception
						raise Solidity.SolidityZeroAddress
					else();
			
			 (* iii) check that contract is not paused (mimic of _beforeTokenTransfer hook) *)
                let hook_check = paused (!s) in 
                if not hook_check then 
                    // if contract is paused
                    raise Solidity.SolidityPaused
                else();
			
			let fromBalance : uint = Solidity.get (!s)._balances from in 
				(* iv) check that fromBalance >= amount *)
				let check_balance = (FStar.UInt256.gte fromBalance amount) in 
				if not check_balance then 
					// if amount > fromBalance
					raise Solidity.SolidityAmountExceedsBalance
				else ();	

				(***	Unchecked part	
							- 	we can surely assume following claims/facts:
									- `_totalSupply` is bounded by `max_uint` 
									  (Solidity automatic check from reforge function)
									- `_totalSupply` is greater [** or equal **] then `fromBalance` 
									  [** if fromBalance contains all available tokens **]
									- `_totalSupply`- `fromBalance` >= `toBalance`
									  since `_totalSupply` holds all available tokens
							 	
							- 	therefore, sum of all balances (totalSupply) is preserved with
								substracting and incrementing the same amount since we verified (checked)
								that amount <= fromBalance
				***)
				let _totalSupply = (!s)._totalSupply in 
				let toBalance = Solidity.get (!s)._balances to in 
				let _ = assume (FStar.UInt256.gte Solidity.max_uint _totalSupply) in 
				let _ = assume (FStar.UInt256.gte _totalSupply fromBalance) in 
				let _ = assume (FStar.UInt256.gte (FStar.UInt256.sub _totalSupply fromBalance) toBalance) in 
				
				let sumBeforeUpdate = FStar.UInt256.add fromBalance toBalance in 
				(*	decrease from's balance by amount  -> amount <= from's balance *)
				s := 	{!s with _balances = Solidity.set (!s)._balances from 
							( FStar.UInt256.sub fromBalance amount )
						};
				
				(*	increment to's balance by amount	*)
				s := 	{!s with _balances = Solidity.set (!s)._balances to 
							( FStar.UInt256.add (Solidity.get (!s)._balances to) amount)
				};

				(* v)  update state with the new event - emit Transfer(from, to, amount); *)
                s := 	{!s with events_ = Transfer from to amount :: (!s).events_};

				(*	ensure that sum of to's and from's balance is equal before and after update
					`proof of the sum preservation`
				*)
				let fromUpdatedBalance = Solidity.get (!s)._balances from in 
				let toUpdatedBalance = Solidity.get (!s)._balances to in 
				let sumAfterUpdate = FStar.UInt256.add fromUpdatedBalance toUpdatedBalance in 
				let _ = assert (FStar.UInt256.eq sumBeforeUpdate sumAfterUpdate) in


		// return updated state
        (Some (), !s)
        with
            // if any other error occurs keep the old state (revert)
            _ -> (None, state)

(* function _burn *)
let _burn 		(state:global_state)
				(account:address)
				(amount:uint)
				: ML (option (unit) * global_state) =
		let s : ref global_state = alloc state in
		try 		
			(* i) check that `account` is not zero address (default address) *)
			let check_from = (FStar.UInt160.eq account default_address) in
			if check_from then 
				// if address is zero address raise an exception
				raise Solidity.SolidityZeroAddress
			else();

			(* ii) check that contract is not paused (mimic of _beforeTokenTransfer hook) *)
			let hook_check = paused (!s) in 
			if not hook_check then 
				// if contract is paused
				raise Solidity.SolidityPaused
			else();

			let accountBalance = Solidity.get (!s)._balances account in 
				(* iii) check that accountBalance >= amount *)
				let check_balance = (FStar.UInt256.gte accountBalance amount) in 
				if not check_balance then 
					// if amount > accountBalance
					raise Solidity.SolidityAmountExceedsBalance
				else ();	
			
			(***	Unchecked part	
						- 	we can surely assume following claims/facts:
									- `_totalSupply` is bounded by `max_uint` 
									  (Solidity automatic check from reforge function)
									- `_totalSupply` is greater [** or equal **] then `accountBalance` 
									  [** if `accountBalance` contains all available tokens **]
			***)
			let _totalSupply = (!s)._totalSupply in 
			let _ = assume (FStar.UInt256.gte Solidity.max_uint _totalSupply) in 
			let _ = assume (FStar.UInt256.gte _totalSupply accountBalance) in 
			
			let differenceBefore = FStar.UInt256.sub _totalSupply accountBalance in 
			(*	decrease account's balance by amount,  `amount <= accountBalance` *)
				s := 	{!s with _balances = Solidity.set (!s)._balances account 
							( FStar.UInt256.sub accountBalance amount )
						};
			
			(*	decrease _totalSupply by amount, `amount <= accountBalance <= _totalSupply` *)
				s := 	{!s with _totalSupply =  ( FStar.UInt256.sub (!s)._totalSupply amount )};
			
			(* iv)  update state with the new event - emit Transfer(account, address(0), amount); *)
                s := 	{!s with events_ = Transfer account default_address amount :: (!s).events_};
			
			(*	ensure that difference between `_totalSupply` and `_balances[account]` remains the 
				same before and after update							
			*)
			let _totalSupplyUpdated = (!s)._totalSupply in 
			let accountBalanceUpdated = Solidity.get (!s)._balances account in 
			let differenceAfter = FStar.UInt256.sub _totalSupplyUpdated accountBalanceUpdated in 
			let _ = assert (FStar.UInt256.eq differenceBefore differenceAfter) in

		// return updated state
        (Some (), !s)
        with
            // if any other error occurs keep the old state (revert)
            _ -> (None, state)