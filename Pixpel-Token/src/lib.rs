#![cfg_attr(not(feature = "std"), no_std)]
use concordium_cis2::*;
use concordium_std::*;

const TOKEN_ID: ContractTokenId = TokenIdUnit();

const TOKEN_METADATA_URL: &str = "https://some.example/token/wccd";

const SUPPORTS_STANDARDS: [StandardIdentifier<'static>; 2] =
    [CIS0_STANDARD_IDENTIFIER, CIS2_STANDARD_IDENTIFIER];

type ContractTokenId = TokenIdUnit;

type ContractTokenAmount = TokenAmountU64;

#[derive(Serial, DeserialWithState, Deletable)]
#[concordium(state_parameter = "S")]
struct AddressState<S> {
    balance:   ContractTokenAmount,
    operators: StateSet<Address, S>,
}

#[derive(Serial, DeserialWithState, StateClone)]
#[concordium(state_parameter = "S")]
struct State<S> {
    token:        StateMap<Address, AddressState<S>, S>,
    implementors: StateMap<StandardIdentifierOwned, Vec<ContractAddress>, S>,
}

#[derive(Serialize, SchemaType)]
struct BurnParams {
    amount:   ContractTokenAmount,
    from:    Address,
}

#[derive(Serialize, SchemaType)]
struct MintParams {
    to:   Receiver,
    amount: ContractTokenAmount,
}

#[derive(Debug, Serialize, SchemaType)]
struct SetImplementorsParams {
    id:           StandardIdentifierOwned,
    implementors: Vec<ContractAddress>,
}

#[derive(Serialize, Debug, PartialEq, Eq, Reject, SchemaType)]
enum CustomContractError {
    #[from(ParseError)]
    ParseParams,
    LogFull,
    LogMalformed,
    InvokeContractError,
    InvokeTransferError,
    CanNotMint,
}

type ContractError = Cis2Error<CustomContractError>;

type ContractResult<A> = Result<A, ContractError>;

impl From<LogError> for CustomContractError {
    fn from(le: LogError) -> Self {
        match le {
            LogError::Full => Self::LogFull,
            LogError::Malformed => Self::LogMalformed,
        }
    }
}

impl<T> From<CallContractError<T>> for CustomContractError {
    fn from(_cce: CallContractError<T>) -> Self { Self::InvokeContractError }
}

impl From<TransferError> for CustomContractError {
    fn from(_te: TransferError) -> Self { Self::InvokeTransferError }
}

impl From<CustomContractError> for ContractError {
    fn from(c: CustomContractError) -> Self { Cis2Error::Custom(c) }
}

impl<S: HasStateApi> State<S> {
    fn new(state_builder: &mut StateBuilder<S>) -> Self {
        State {
            token:        state_builder.new_map(),
            implementors: state_builder.new_map(),
        }
    }

    fn balance(
        &self,
        token_id: &ContractTokenId,
        address: &Address,
    ) -> ContractResult<ContractTokenAmount> {
        ensure_eq!(token_id, &TOKEN_ID, ContractError::InvalidTokenId);
        Ok(self.token.get(address).map(|s| s.balance).unwrap_or_else(|| 0u64.into()))
    }

    fn is_operator(&self, address: &Address, owner: &Address) -> bool {
        self.token
            .get(owner)
            .map(|address_state| address_state.operators.contains(address))
            .unwrap_or(false)
    }

    fn transfer(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        from: &Address,
        to: &Address,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID, ContractError::InvalidTokenId);
        if amount == 0u64.into() {
            return Ok(());
        }
        {
            let mut from_state =
                self.token.get_mut(from).ok_or(ContractError::InsufficientFunds)?;
            ensure!(from_state.balance >= amount, ContractError::InsufficientFunds);
            from_state.balance -= amount;
        }
        let mut to_state = self.token.entry(*to).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });
        to_state.balance += amount;

        Ok(())
    }

    fn add_operator(
        &mut self,
        owner: &Address,
        operator: &Address,
        state_builder: &mut StateBuilder<S>,
    ) {
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });
        owner_state.operators.insert(*operator);
    }

    fn remove_operator(&mut self, owner: &Address, operator: &Address) {
        self.token.entry(*owner).and_modify(|address_state| {
            address_state.operators.remove(operator);
        });
    }

    fn mint(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        owner: &Address,
        state_builder: &mut StateBuilder<S>,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID, ContractError::InvalidTokenId);
        let mut owner_state = self.token.entry(*owner).or_insert_with(|| AddressState {
            balance:   0u64.into(),
            operators: state_builder.new_set(),
        });

        owner_state.balance += amount;
        Ok(())
    }

    fn burn(
        &mut self,
        token_id: &ContractTokenId,
        amount: ContractTokenAmount,
        owner: &Address,
    ) -> ContractResult<()> {
        ensure_eq!(token_id, &TOKEN_ID, ContractError::InvalidTokenId);
        if amount == 0u64.into() {
            return Ok(());
        }

        let mut from_state = self.token.get_mut(owner).ok_or(ContractError::InsufficientFunds)?;
        ensure!(from_state.balance >= amount, ContractError::InsufficientFunds);
        from_state.balance -= amount;

        Ok(())
    }

    fn have_implementors(&self, std_id: &StandardIdentifierOwned) -> SupportResult {
        if let Some(addresses) = self.implementors.get(std_id) {
            SupportResult::SupportBy(addresses.to_vec())
        } else {
            SupportResult::NoSupport
        }
    }

    fn set_implementors(
        &mut self,
        std_id: StandardIdentifierOwned,
        implementors: Vec<ContractAddress>,
    ) {
        self.implementors.insert(std_id, implementors);
    }
}

#[init(contract = "Pixpel-Token", enable_logger)]
fn contract_init<S: HasStateApi>(
    ctx: &impl HasInitContext,
    state_builder: &mut StateBuilder<S>,
    logger: &mut impl HasLogger,
) -> InitResult<State<S>> {
    let state = State::new(state_builder);
    let invoker = Address::Account(ctx.init_origin());
    logger.log(&Cis2Event::Mint(MintEvent {
        token_id: TOKEN_ID,
        amount:   ContractTokenAmount::from(0u64),
        owner:    invoker,
    }))?;

    logger.log(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(TokenMetadataEvent {
        token_id:     TOKEN_ID,
        metadata_url: MetadataUrl {
            url:  String::from(TOKEN_METADATA_URL),
            hash: None,
        },
    }))?;

    Ok(state)
}

#[receive(
    contract = "Pixpel-Token",
    name = "mint",
    parameter = "MintParams",
    enable_logger,
    mutable,
)]
fn contract_mint<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let params: MintParams = ctx.parameter_cursor().get()?;
    let sender = ctx.sender();
    ensure!(sender.matches_account(&ctx.owner()), ContractError::Unauthorized);

    let receive_address = params.to.address();

    let (state, state_builder) = host.state_and_builder();
    state.mint(&TOKEN_ID, params.amount, &receive_address, state_builder)?;

    logger.log(&Cis2Event::Mint(MintEvent {
        token_id: TOKEN_ID,
        amount:   params.amount,
        owner:    sender,
    }))?;

    if sender != receive_address {
        logger.log(&Cis2Event::Transfer(TransferEvent {
            token_id: TOKEN_ID,
            amount:   params.amount,
            from:     sender,
            to:       receive_address,
        }))?;
    }

    Ok(())
}

#[receive(
    contract = "Pixpel-Token",
    name = "burn",
    parameter = "UnwrapParams",
    enable_logger,
    mutable
)]
fn contract_burn<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    let params: BurnParams = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();
    let state = host.state_mut();
    ensure!(
        sender == params.from || state.is_operator(&sender, &params.from),
        ContractError::Unauthorized
    );

    // Update the state.
    state.burn(&TOKEN_ID, params.amount, &params.from)?;

    // Log the burning of tokens.
    logger.log(&Cis2Event::Burn(BurnEvent {
        token_id: TOKEN_ID,
        amount:   params.amount,
        owner:    params.from,
    }))?;

    Ok(())
}

// Contract functions required by CIS2

#[allow(dead_code)]
type TransferParameter = TransferParams<ContractTokenId, ContractTokenAmount>;

#[receive(
    contract = "Pixpel-Token",
    name = "transfer",
    parameter = "TransferParameter",
    enable_logger,
    mutable
)]
fn contract_transfer<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let TransferParams(transfers): TransferParameter = ctx.parameter_cursor().get()?;
    let sender = ctx.sender();

    for Transfer {
        token_id,
        amount,
        from,
        to,
        data,
    } in transfers
    {
        let (state, builder) = host.state_and_builder();
        // Authenticate the sender for this transfer
        ensure!(from == sender || state.is_operator(&sender, &from), ContractError::Unauthorized);
        let to_address = to.address();
        state.transfer(&token_id, amount, &from, &to_address, builder)?;

        logger.log(&Cis2Event::Transfer(TransferEvent {
            token_id,
            amount,
            from,
            to: to_address,
        }))?;

        if let Receiver::Contract(address, function) = to {
            let parameter = OnReceivingCis2Params {
                token_id,
                amount,
                from,
                data,
            };
            host.invoke_contract(
                &address,
                &parameter,
                function.as_entrypoint_name(),
                Amount::zero(),
            )?;
        }
    }
    Ok(())
}

#[receive(
    contract = "Pixpel-Token",
    name = "updateOperator",
    parameter = "UpdateOperatorParams",
    enable_logger,
    mutable
)]
fn contract_update_operator<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
    logger: &mut impl HasLogger,
) -> ContractResult<()> {
    // Parse the parameter.
    let UpdateOperatorParams(params) = ctx.parameter_cursor().get()?;
    // Get the sender who invoked this contract function.
    let sender = ctx.sender();

    let (state, state_builder) = host.state_and_builder();
    for param in params {
        // Update the operator in the state.
        match param.update {
            OperatorUpdate::Add => state.add_operator(&sender, &param.operator, state_builder),
            OperatorUpdate::Remove => state.remove_operator(&sender, &param.operator),
        }

        logger.log(&Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
            UpdateOperatorEvent {
                owner:    sender,
                operator: param.operator,
                update:   param.update,
            },
        ))?;
    }

    Ok(())
}

type ContractBalanceOfQueryParams = BalanceOfQueryParams<ContractTokenId>;

type ContractBalanceOfQueryResponse = BalanceOfQueryResponse<ContractTokenAmount>;

#[receive(
    contract = "Pixpel-Token",
    name = "balanceOf",
    parameter = "ContractBalanceOfQueryParams",
    return_value = "ContractBalanceOfQueryResponse",
)]
fn contract_balance_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<ContractBalanceOfQueryResponse> {
    // Parse the parameter.
    let params: ContractBalanceOfQueryParams = ctx.parameter_cursor().get()?;
    // Build the response.
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        // Query the state for balance.
        let amount = host.state().balance(&query.token_id, &query.address)?;
        response.push(amount);
    }
    let result = ContractBalanceOfQueryResponse::from(response);
    Ok(result)
}

#[receive(
    contract = "Pixpel-Token",
    name = "operatorOf",
    parameter = "OperatorOfQueryParams",
    return_value = "OperatorOfQueryResponse",
)]
fn contract_operator_of<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<OperatorOfQueryResponse> {
    let params: OperatorOfQueryParams = ctx.parameter_cursor().get()?;
    let mut response = Vec::with_capacity(params.queries.len());
    for query in params.queries {
        let is_operator = host.state().is_operator(&query.address, &query.owner);
        response.push(is_operator);
    }
    let result = OperatorOfQueryResponse::from(response);
    Ok(result)
}

pub type ContractTokenMetadataQueryParams = TokenMetadataQueryParams<ContractTokenId>;

#[receive(
    contract = "Pixpel-Token",
    name = "tokenMetadata",
    parameter = "ContractTokenMetadataQueryParams",
    return_value = "TokenMetadataQueryResponse",
)]
fn contract_token_metadata<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    _host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<TokenMetadataQueryResponse> {
    let params: ContractTokenMetadataQueryParams = ctx.parameter_cursor().get()?;

    let mut response = Vec::with_capacity(params.queries.len());
    for token_id in params.queries {
        ensure_eq!(token_id, TOKEN_ID, ContractError::InvalidTokenId);

        let metadata_url = MetadataUrl {
            url:  TOKEN_METADATA_URL.to_string(),
            hash: None,
        };
        response.push(metadata_url);
    }
    let result = TokenMetadataQueryResponse::from(response);
    Ok(result)
}

#[receive(
    contract = "Pixpel-Token",
    name = "supports",
    parameter = "SupportsQueryParams",
    return_value = "SupportsQueryResponse",
)]
fn contract_supports<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<SupportsQueryResponse> {
    let params: SupportsQueryParams = ctx.parameter_cursor().get()?;

    let mut response = Vec::with_capacity(params.queries.len());
    for std_id in params.queries {
        if SUPPORTS_STANDARDS.contains(&std_id.as_standard_identifier()) {
            response.push(SupportResult::Support);
        } else {
            response.push(host.state().have_implementors(&std_id));
        }
    }
    let result = SupportsQueryResponse::from(response);
    Ok(result)
}

#[receive(
    contract = "Pixpel-Token",
    name = "setImplementors",
    parameter = "SetImplementorsParams",
    mutable
)]
fn contract_set_implementor<S: HasStateApi>(
    ctx: &impl HasReceiveContext,
    host: &mut impl HasHost<State<S>, StateApiType = S>,
) -> ContractResult<()> {
    ensure!(ctx.sender().matches_account(&ctx.owner()), ContractError::Unauthorized);
    let params: SetImplementorsParams = ctx.parameter_cursor().get()?;
    host.state_mut().set_implementors(params.id, params.implementors);
    Ok(())
}

// Tests

#[concordium_cfg_test]
mod tests {
    use super::*;
    use test_infrastructure::*;

    const ACCOUNT_0: AccountAddress = AccountAddress([0u8; 32]);
    const ADDRESS_0: Address = Address::Account(ACCOUNT_0);
    const ACCOUNT_1: AccountAddress = AccountAddress([1u8; 32]);
    const ADDRESS_1: Address = Address::Account(ACCOUNT_1);

    /// Test helper function which creates a contract state where ADDRESS_0 owns
    /// 400 tokens.
    fn initial_state<S: HasStateApi>(state_builder: &mut StateBuilder<S>) -> State<S> {
        let mut state = State::new(state_builder);
        state
            .mint(&TOKEN_ID, 400u64.into(), &ADDRESS_0, state_builder)
            .expect_report("Failed to setup state");
        state
    }

    /// Test initialization succeeds and the tokens are owned by the contract
    /// instantiater and the appropriate events are logged.
    #[concordium_test]
    fn test_init() {
        // Setup the context
        let mut ctx = TestInitContext::empty();
        ctx.set_init_origin(ACCOUNT_0);

        let mut logger = TestLogger::init();
        let mut builder = TestStateBuilder::new();

        // Call the contract function.
        let result = contract_init(&ctx, &mut builder, &mut logger);

        // Check the result
        let state = result.expect_report("Contract initialization failed");

        // Check the state
        claim_eq!(state.token.iter().count(), 0, "Only one token is initialized");
        let balance0 =
            state.balance(&TOKEN_ID, &ADDRESS_0).expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            0u64.into(),
            "No initial tokens are owned by the contract instantiater"
        );

        // Check the logs
        claim_eq!(logger.logs.len(), 2, "Exactly one event should be logged");
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::Mint(MintEvent {
                owner:    ADDRESS_0,
                token_id: TOKEN_ID,
                amount:   ContractTokenAmount::from(0),
            }))),
            "Missing event for minting the token"
        );
        claim!(
            logger.logs.contains(&to_bytes(&Cis2Event::TokenMetadata::<_, ContractTokenAmount>(
                TokenMetadataEvent {
                    token_id:     TOKEN_ID,
                    metadata_url: MetadataUrl {
                        url:  String::from(TOKEN_METADATA_URL),
                        hash: None,
                    },
                }
            ))),
            "Missing event with metadata for the token"
        );
    }

    /// Test transfer succeeds, when `from` is the sender.
    #[concordium_test]
    fn test_transfer_account() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        // and parameter.
        let transfer = Transfer {
            token_id: TOKEN_ID,
            amount:   ContractTokenAmount::from(100),
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let mut state = State::new(&mut state_builder);
        state
            .mint(&TOKEN_ID, 400.into(), &ADDRESS_0, &mut state_builder)
            .expect_report("Failed to setup state");
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);
        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let balance0 = host
            .state()
            .balance(&TOKEN_ID, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        let balance1 = host
            .state()
            .balance(&TOKEN_ID, &ADDRESS_1)
            .expect_report("Token is expected to exist");
        claim_eq!(
            balance0,
            300.into(),
            "Token owner balance should be decreased by the transferred amount"
        );
        claim_eq!(
            balance1,
            100.into(),
            "Token receiver balance should be increased by the transferred amount"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::Transfer(TransferEvent {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID,
                amount:   ContractTokenAmount::from(100),
            })),
            "Incorrect event emitted"
        )
    }

    /// Test transfer token fails, when sender is neither the owner or an
    /// operator of the owner.
    #[concordium_test]
    fn test_transfer_not_authorized() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);

        // and parameter.
        let transfer = Transfer {
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            token_id: TOKEN_ID,
            amount:   ContractTokenAmount::from(100),
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);
        // Check the result.
        let err = result.expect_err_report("Expected to fail");
        claim_eq!(err, ContractError::Unauthorized, "Error is expected to be Unauthorized")
    }

    /// Test transfer succeeds when sender is not the owner, but is an operator
    /// of the owner.
    #[concordium_test]
    fn test_operator_transfer() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_1);

        // and parameter.
        let transfer = Transfer {
            from:     ADDRESS_0,
            to:       Receiver::from_account(ACCOUNT_1),
            token_id: TOKEN_ID,
            amount:   ContractTokenAmount::from(100),
            data:     AdditionalData::empty(),
        };
        let parameter = TransferParams::from(vec![transfer]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let mut state = initial_state(&mut state_builder);
        state.add_operator(&ADDRESS_0, &ADDRESS_1, &mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_transfer(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        let balance0 = host
            .state()
            .balance(&TOKEN_ID, &ADDRESS_0)
            .expect_report("Token is expected to exist");
        let balance1 = host
            .state()
            .balance(&TOKEN_ID, &ADDRESS_1)
            .expect_report("Token is expected to exist");
        claim_eq!(balance0, 300.into()); //, "Token owner balance should be decreased by the transferred amount");
        claim_eq!(
            balance1,
            100.into(),
            "Token receiver balance should be increased by the transferred amount"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "Only one event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::Transfer(TransferEvent {
                from:     ADDRESS_0,
                to:       ADDRESS_1,
                token_id: TOKEN_ID,
                amount:   ContractTokenAmount::from(100),
            })),
            "Incorrect event emitted"
        )
    }

    /// Test adding an operator succeeds and the appropriate event is logged.
    #[concordium_test]
    fn test_add_operator() {
        // Setup the context
        let mut ctx = TestReceiveContext::empty();
        ctx.set_sender(ADDRESS_0);

        // and parameter.
        let update = UpdateOperator {
            operator: ADDRESS_1,
            update:   OperatorUpdate::Add,
        };
        let parameter = UpdateOperatorParams(vec![update]);
        let parameter_bytes = to_bytes(&parameter);
        ctx.set_parameter(&parameter_bytes);

        let mut logger = TestLogger::init();
        let mut state_builder = TestStateBuilder::new();
        let state = initial_state(&mut state_builder);
        let mut host = TestHost::new(state, state_builder);

        // Call the contract function.
        let result: ContractResult<()> = contract_update_operator(&ctx, &mut host, &mut logger);

        // Check the result.
        claim!(result.is_ok(), "Results in rejection");

        // Check the state.
        claim!(host.state().is_operator(&ADDRESS_1, &ADDRESS_0), "Account should be an operator");

        // Checking that `ADDRESS_1` is an operator in the query response of the
        // `contract_operator_of` function as well.
        // Setup parameter.
        let operator_of_query = OperatorOfQuery {
            address: ADDRESS_1,
            owner:   ADDRESS_0,
        };

        let operator_of_query_vector = OperatorOfQueryParams {
            queries: vec![operator_of_query],
        };
        let parameter_bytes = to_bytes(&operator_of_query_vector);

        ctx.set_parameter(&parameter_bytes);

        // Checking the return value of the `contract_operator_of` function
        let result: ContractResult<OperatorOfQueryResponse> = contract_operator_of(&ctx, &host);

        claim_eq!(
            result.expect_report("Failed getting result value").0,
            [true],
            "Account should be an operator in the query response"
        );

        // Check the logs.
        claim_eq!(logger.logs.len(), 1, "One event should be logged");
        claim_eq!(
            logger.logs[0],
            to_bytes(&Cis2Event::<ContractTokenId, ContractTokenAmount>::UpdateOperator(
                UpdateOperatorEvent {
                    owner:    ADDRESS_0,
                    operator: ADDRESS_1,
                    update:   OperatorUpdate::Add,
                }
            )),
            "Incorrect event emitted"
        )
    }
}