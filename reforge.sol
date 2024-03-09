// SPDX-License-Identifier: MIT 
pragma solidity 0.8;

contract ARYZE_eEUR 
{

   // ****** Function _mint and global parameters from  from ERC20Upgradeble.sol *******
    uint256 private _totalSupply; // presents the total number of tokens in the existence
    mapping(address => uint256) private _balances;
    event Transfer(address indexed from, address indexed to, uint256 value);

    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

       /* Following hook checks that the contract is not in paused state and will
          be ommited in the verification process for the simplicity */

       // _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount; // if overflow is suppose to happen it would happen 
                                // here since there is at most _totalSupply + amount tokens available
        unchecked {
            // Overflow not possible: balance + amount is at most totalSupply + amount, which is checked above.
            _balances[account] += amount;
        }
        emit Transfer(address(0), account, amount);

        //_afterTokenTransfer(address(0), account, amount);
    }
    // **************************************************************************************

    mapping(string => bool) private _transactions; // Bridge transactions for prevent recurrence of the transaction


    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    struct RoleData {
        mapping(address => bool) members;
        bytes32 adminRole;
    }

    mapping(bytes32 => RoleData) private _roles;

    modifier onlyRole(bytes32 role) {
        _checkRole(role, _msgSender());
        _;
    }

    function hasRole(bytes32 role, address account) public view virtual returns (bool) {
        return _roles[role].members[account];
    }

    function _checkRole(bytes32 role, address account) internal view virtual {
        if (!hasRole(role, account)) {
            revert(
                string(
                    //abi.encodePacked(
                        "AccessControl: account "//,
                        //StringsUpgradeable.toHexString(uint160(account), 20),
                        //" is missing role ",
                        //StringsUpgradeable.toHexString(uint256(role), 32)
                    //)
                )
            );
        }
    }

    bytes32 public constant PAUSER_ROLE = keccak256("PAUSER_ROLE");
    bytes32 public constant MINTER_ROLE = keccak256("MINTER_ROLE");
    bytes32 public constant UPGRADER_ROLE = keccak256("UPGRADER_ROLE");
    bytes32 public constant BRIDGE_OWNER_ROLE = keccak256("BRIDGE_OWNER_ROLE");

    address payable private _bridgeOwner; // receives transactions fee in native currency

    event Reforged(address indexed account, uint256 amount, string indexed transaction);

    function reforge(
        address to,
        uint256 amount,
        uint256 fee,
        string memory rate,
        uint256 sourceChainId,
        string memory transaction   // transaction hash - 64 long hexadeciaml number  + '0x' = 66 characters long string 
    ) public onlyRole(BRIDGE_OWNER_ROLE) onlyRole(MINTER_ROLE) {
        require(_transactions[transaction] == false, "Already processed!");
         _mint(to, amount);
        if (fee != 0) {
            _mint(_bridgeOwner, fee);
        }
        _transactions[transaction] = true;
        emit Reforged(to, amount, transaction);
    }
}