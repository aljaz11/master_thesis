// SPDX-License-Identifier: MIT 
pragma solidity 0.8;

contract ARYZE_eEUR 
{

    mapping(string => bool) private _transactions; // Bridge transactions for prevent recurrence of the transaction

    function reforge(
        address to,
        uint256 amount,
        uint256 fee,
        string memory rate,
        uint256 sourceChainId,
        string memory transaction   // transaction hash - 64 long hexadeciaml number  + '0x' = 66 characters long string 
    ) public onlyRole(BRIDGE_OWNER_ROLE) onlyRole(MINTER_ROLE) {
        require(_transactions[transaction] == false, "Already processed!");
        /*
         _mint(to, amount);
        if (fee != 0) {
            _mint(_bridgeOwner, fee);
        }
        */
        _transactions[transaction] = true;
        emit Reforged(to, amount, transaction);
    }
}