// SPDX-License-Identifier: MIT 
pragma solidity 0.8;

contract ARYZE_eEUR 
{   function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }
    // ****************     from ERC20BurnableUpgradeable.sol   ****************

    function burn(uint256 amount) public virtual {
        _burn(_msgSender(), amount);
    }

    // ****************     from ERC20Upgradeable.sol           ****************
    // default address for roles
    address private multiSigTreasury;


    uint256 private _totalSupply; // presents the total number of tokens in the existence
    mapping(address => uint256) private _balances;

    function transfer(address to, uint256 amount) public virtual returns (bool) {
        address owner = _msgSender();
        _transfer(owner, to, amount);
        return true;
    }

    event Transfer(address indexed from, address indexed to, uint256 value);

    function _transfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(from, to, amount);

        uint256 fromBalance = _balances[from];
        require(fromBalance >= amount, "ERC20: transfer amount exceeds balance");
        unchecked {
            _balances[from] = fromBalance - amount;
            // Overflow not possible: the sum of all balances is capped by totalSupply, and the sum is preserved by
            // decrementing then incrementing.
            _balances[to] += amount;
        }

        emit Transfer(from, to, amount);

        // _afterTokenTransfer(from, to, amount);
    }


    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
            // Overflow not possible: amount <= accountBalance <= totalSupply.
            _totalSupply -= amount;
        }

        emit Transfer(account, address(0), amount);

        //_afterTokenTransfer(account, address(0), amount);
    }

    //  ****************    from ARYZE_eEUR.sol         ****************
    // feeTresury (default value is multiSigTreasury: 0xaB23968d766D445BC9b370512d3085c345AcB235)
    address private _feeTreasury;
    
    // global variable to indicate if bridge is paused (default is false)
    bool private _bridgePaused;    

    // global varibale representing bridge transaction fee in native currency (default is 0)
    uint256 private _minimumBridgeFee;  

    
    //Bridge transactions fee percentage (10**6 = 1%) (default is 3*100000 == 0.3%)
    uint256 private _bridgeFee;

    // global mapping that maps chain_id (uint256) to the address of specific token (e.g. eEUR)
    // e.g., maps Ethereum chain to eEUR token
    mapping(uint256 => address) private _sameTokens;

    // global variable representing minimal reqauired amount for SendToChain (default value is 10^22)
    uint256 private _minimumSendToChainAmount;

    // Global variable from PausableUpgreadale.sol
    bool private _paused;

    // Global variable representing the account that receives transaction fee (default unknown - could be zero address)
    address payable private _bridgeOwner;

    // Function from PausableUpgreadable.sol
    function paused() public view virtual returns (bool) {
        return _paused;
    }
    
    // Function from PausableUpgreadable.sol
    function _requireNotPaused() internal view virtual {
        require(!paused(), "Pausable: paused");
    }

    // Modifier from PausableUpgreadable.sol
    modifier whenNotPaused() {
        _requireNotPaused();
        _;
    }

    // Hook from main contract ARYZE_eEUR.sol that overrides the original hook
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal whenNotPaused {}

    event SentToChain(
        address indexed account,
        uint256 amount,
        uint256 fromChainId,
        uint256 indexed destinationChainId,
        address indexed destinationToken
    );



    function sendToChain(
        uint256 amount,
        uint256 destinationChainId,
        address destinationToken
    ) public payable {
        require(_bridgePaused == false, "Bridge paused");
        require(msg.value >= _minimumBridgeFee, "Fee too small");
        if (_sameTokens[destinationChainId] != destinationToken) {
            require(amount >= _minimumSendToChainAmount, "Amount < Minimum amount");
        }
        require(address(0) != destinationToken, "Destination token undefined");
        uint256 fee = (amount * _bridgeFee) / 100000000; // fee 1% == 1000000
        require(amount > fee, "Fee > 100%");
        uint256 res = amount - fee;
        transfer(_feeTreasury, fee);
        burn(res);
        _bridgeOwner.transfer(msg.value);
        emit SentToChain(msg.sender, amount - fee, block.chainid, destinationChainId, destinationToken);
    }
}