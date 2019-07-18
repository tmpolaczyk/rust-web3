//! Ethereum Contract Interface

use ethabi;

use crate::api::{Eth, Namespace};
use crate::confirm;
use crate::contract::tokens::{Detokenize, Tokenize};
use crate::types::{Address, BlockNumber, Bytes, CallRequest, TransactionCondition, TransactionRequest, H256, U256};
use crate::Transport;
use std::{collections::HashMap, hash::Hash, time};

use crate::ethereum_tx_sign::RawTransaction;
use futures::Future;
use std::time::Duration;
use crate::types::{TransactionReceipt};

pub mod deploy;
mod error;
mod result;
pub mod tokens;

pub use crate::contract::error::Error;
pub use crate::contract::result::{CallFuture, QueryResult};

/// Contract Call/Query Options
#[derive(Default, Debug, Clone, PartialEq)]
pub struct Options {
    /// Fixed gas limit
    pub gas: Option<U256>,
    /// Fixed gas price
    pub gas_price: Option<U256>,
    /// Value to transfer
    pub value: Option<U256>,
    /// Fixed transaction nonce
    pub nonce: Option<U256>,
    /// A conditon to satisfy before including transaction.
    pub condition: Option<TransactionCondition>,
}

impl Options {
    /// Create new default `Options` object with some modifications.
    pub fn with<F>(func: F) -> Options
    where
        F: FnOnce(&mut Options),
    {
        let mut options = Options::default();
        func(&mut options);
        options
    }
}

/// Ethereum Contract Interface
#[derive(Debug, Clone)]
pub struct Contract<T: Transport> {
    address: Address,
    eth: Eth<T>,
    abi: ethabi::Contract,
}

impl<T: Transport> Contract<T> {
    /// Creates deployment builder for a contract given it's ABI in JSON.
    pub fn deploy(eth: Eth<T>, json: &[u8]) -> Result<deploy::Builder<T>, ethabi::Error> {
        let abi = ethabi::Contract::load(json)?;
        Ok(deploy::Builder {
            eth,
            abi,
            options: Options::default(),
            confirmations: 1,
            poll_interval: time::Duration::from_secs(7),
            linker: HashMap::default(),
        })
    }

    /// test
    pub fn deploy_from_truffle<S>(
        eth: Eth<T>,
        json: &[u8],
        linker: HashMap<S, Address>,
    ) -> Result<deploy::Builder<T>, ethabi::Error>
    where
        S: AsRef<str> + Eq + Hash,
    {
        let abi = ethabi::Contract::load(json)?;
        let linker: HashMap<String, Address> = linker.into_iter().map(|(s, a)| (s.as_ref().to_string(), a)).collect();
        Ok(deploy::Builder {
            eth,
            abi,
            options: Options::default(),
            confirmations: 1,
            poll_interval: time::Duration::from_secs(7),
            linker,
        })
    }
}

impl<T: Transport> Contract<T> {
    /// Creates new Contract Interface given blockchain address and ABI
    pub fn new(eth: Eth<T>, address: Address, abi: ethabi::Contract) -> Self {
        Contract { address, eth, abi }
    }

    /// Creates new Contract Interface given blockchain address and JSON containing ABI
    pub fn from_json(eth: Eth<T>, address: Address, json: &[u8]) -> Result<Self, ethabi::Error> {
        let abi = ethabi::Contract::load(json)?;
        Ok(Self::new(eth, address, abi))
    }

    /// Returns contract address
    pub fn address(&self) -> Address {
        self.address
    }

    /// Returns contract abi
    pub fn abi(&self) -> &ethabi::Contract {
        &self.abi
    }

    /// Returns contract eth
    pub fn eth(&self) -> &Eth<T> {
        &self.eth
    }

    /// Execute a contract function
    pub fn call<P>(&self, func: &str, params: P, from: Address, options: Options) -> CallFuture<H256, T::Out>
    where
        P: Tokenize,
    {
        self.abi
            .function(func)
            .and_then(|function| function.encode_input(&params.into_tokens()))
            .map(move |data| {
                let Options {
                    gas,
                    gas_price,
                    value,
                    nonce,
                    condition,
                } = options;

                self.eth
                    .send_transaction(TransactionRequest {
                        from,
                        to: Some(self.address),
                        gas,
                        gas_price,
                        value,
                        nonce,
                        data: Some(Bytes(data)),
                        condition,
                    })
                    .into()
            })
            .unwrap_or_else(Into::into)
    }

    /// Execute a contract function and wait for confirmations
    pub fn call_with_confirmations<P>(
        &self,
        func: &str,
        params: P,
        from: Address,
        options: Options,
        confirmations: usize,
    ) -> confirm::SendTransactionWithConfirmation<T>
    where
        P: Tokenize,
    {
        let poll_interval = time::Duration::from_secs(1);

        self.abi
            .function(func)
            .and_then(|function| function.encode_input(&params.into_tokens()))
            .map(|fn_data| {
                let transaction_request = TransactionRequest {
                    from,
                    to: Some(self.address),
                    gas: options.gas,
                    gas_price: options.gas_price,
                    value: options.value,
                    nonce: options.nonce,
                    data: Some(Bytes(fn_data)),
                    condition: options.condition,
                };

                confirm::send_transaction_with_confirmation(
                    self.eth.transport().clone(),
                    transaction_request,
                    poll_interval,
                    confirmations,
                )
            })
            .unwrap_or_else(|e| {
                // TODO [ToDr] SendTransactionWithConfirmation should support custom error type (so that we can return
                // `contract::Error` instead of more generic `Error`.
                confirm::SendTransactionWithConfirmation::from_err(
                    self.eth.transport().clone(),
                    crate::error::Error::Decoder(format!("{:?}", e)),
                )
            })
    }

    /// Estimate gas required for this function call.
    pub fn estimate_gas<P>(&self, func: &str, params: P, from: Address, options: Options) -> CallFuture<U256, T::Out>
    where
        P: Tokenize,
    {
        self.abi
            .function(func)
            .and_then(|function| function.encode_input(&params.into_tokens()))
            .map(|data| {
                self.eth
                    .estimate_gas(
                        CallRequest {
                            from: Some(from),
                            to: self.address,
                            gas: options.gas,
                            gas_price: options.gas_price,
                            value: options.value,
                            data: Some(Bytes(data)),
                        },
                        None,
                    )
                    .into()
            })
            .unwrap_or_else(Into::into)
    }

    /// Same as `call`, but sign the transaction locally with the given private key
    pub fn call_raw<P>(
        &self,
        func: &str,
        params: P,
        from: Address,
        private_key: H256,
        options: Options,
    ) -> Box<dyn Future<Item = H256, Error = crate::error::Error> + Send>
    where
        P: Tokenize,
        T: Send + 'static,
        T::Out: Send,
    {
        self.abi()
            .function(func)
            .and_then(|function| function.encode_input(&params.into_tokens()))
            .map(move |data| {
                // To build a raw transaction, we need:
                // nonce: eth.transaction_count()
                // gas_price: eth.gas_price()
                // gas: eth.estimate_gas()

                let eth = self.eth().clone();
                let eth1 = eth.clone();
                let eth2 = eth.clone();
                let to = self.address();
                let value = options.value;
                let fut_nonce = eth.transaction_count(from, Some(BlockNumber::Pending));
                let fut_gas_price = eth.gas_price();
                let fut: Box<dyn Future<Item = H256, Error = crate::error::Error> + Send> = Box::new(
                    fut_nonce
                        .join(fut_gas_price)
                        .and_then(move |(nonce, gas_price)| {
                            let call_request = CallRequest {
                                from: Some(from),
                                to,
                                gas: None,
                                gas_price: Some(gas_price),
                                value,
                                data: Some(Bytes(data.clone())),
                            };
                            eth1.estimate_gas(call_request, None)
                                .map(move |gas| (nonce, gas_price, gas, data))
                        })
                        .and_then(move |(nonce, gas_price, gas, data)| {
                            let raw_tx = RawTransaction {
                                nonce,
                                to: Some(to),
                                value: value.unwrap_or_default(),
                                gas_price,
                                gas,
                                data,
                            };
                            let chain_id = 0x01;
                            let signed_tx = raw_tx.sign(&private_key, chain_id);
                            /*
                            self.eth
                                .send_transaction(TransactionRequest {
                                    from,
                                    to: Some(self.address().clone()),
                                    gas: options.gas,
                                    gas_price: options.gas_price,
                                    value: options.value,
                                    nonce: options.nonce,
                                    data: Some(Bytes(data)),
                                    condition: options.condition,
                                })
                                .into()
                                */
                            eth2.send_raw_transaction(signed_tx.into())
                        }),
                );

                fut
            })
            // TODO: error handling
            .unwrap_or_else(|_e| Box::new(futures::failed(crate::error::Error::Internal)))
    }

    /// Same as `call_with_confirmations`, but sign the transaction locally with the given private key
    pub fn call_with_confirmations_raw<P>(
        &self,
        func: &str,
        params: P,
        from: Address,
        private_key: H256,
        options: Options,
        confirmations: usize,
    ) -> Box<dyn Future<Item = TransactionReceipt, Error = crate::error::Error> + Send>
    where
        P: Tokenize,
        T: Send + 'static,
        T::Out: Send,
    {
        let poll_interval = Duration::from_secs(1);

        self.abi()
            .function(func)
            .and_then(|function| function.encode_input(&params.into_tokens()))
            .map(move |data| {
                // To build a raw transaction, we need:
                // nonce: eth.transaction_count()
                // gas_price: eth.gas_price()
                // gas: eth.estimate_gas()

                let eth = self.eth().clone();
                let eth1 = eth.clone();
                let eth2 = eth.clone();
                let to = self.address();
                let value = options.value;
                let fut_nonce = eth.transaction_count(from, Some(BlockNumber::Pending));
                let fut_gas_price = eth.gas_price();
                let fut: Box<dyn Future<Item = TransactionReceipt, Error = crate::error::Error> + Send> =
                    Box::new(
                        fut_nonce
                            .join(fut_gas_price)
                            .and_then(move |(nonce, gas_price)| {
                                let call_request = CallRequest {
                                    from: Some(from),
                                    to,
                                    gas: None,
                                    gas_price: Some(gas_price),
                                    value,
                                    data: Some(Bytes(data.clone())),
                                };
                                eth1.estimate_gas(call_request, None)
                                    .map(move |gas| (nonce, gas_price, gas, data))
                            })
                            .and_then(move |(nonce, gas_price, gas, data)| {
                                let raw_tx = RawTransaction {
                                    nonce,
                                    to: Some(to),
                                    value: value.unwrap_or_default(),
                                    gas_price,
                                    gas,
                                    data,
                                };
                                let chain_id = 0x01;
                                let signed_tx = raw_tx.sign(&private_key, chain_id);
                                /*
                                self.eth
                                    .send_transaction(TransactionRequest {
                                        from,
                                        to: Some(self.address().clone()),
                                        gas: options.gas,
                                        gas_price: options.gas_price,
                                        value: options.value,
                                        nonce: options.nonce,
                                        data: Some(Bytes(data)),
                                        condition: options.condition,
                                    })
                                    .into()
                                    */
                                confirm::send_raw_transaction_with_confirmation(
                                    eth2.transport().clone(),
                                    signed_tx.into(),
                                    poll_interval,
                                    confirmations,
                                )
                            }),
                    );

                fut
            })
            // TODO: error handling
            .unwrap_or_else(|_e| Box::new(futures::failed(crate::error::Error::Internal)))
    }

    /// Call constant function
    pub fn query<R, A, B, P>(
        &self,
        func: &str,
        params: P,
        from: A,
        options: Options,
        block: B,
    ) -> QueryResult<R, T::Out>
    where
        R: Detokenize,
        A: Into<Option<Address>>,
        B: Into<Option<BlockNumber>>,
        P: Tokenize,
    {
        self.abi
            .function(func)
            .and_then(|function| {
                function
                    .encode_input(&params.into_tokens())
                    .map(|call| (call, function))
            })
            .map(|(call, function)| {
                let result = self.eth.call(
                    CallRequest {
                        from: from.into(),
                        to: self.address,
                        gas: options.gas,
                        gas_price: options.gas_price,
                        value: options.value,
                        data: Some(Bytes(call)),
                    },
                    block.into(),
                );
                QueryResult::new(result, function.clone())
            })
            .unwrap_or_else(Into::into)
    }
}

#[cfg(test)]
mod tests {
    use super::{Contract, Options};
    use crate::api::{self, Namespace};
    use crate::helpers::tests::TestTransport;
    use crate::rpc;
    use crate::types::{Address, BlockNumber, H256, U256};
    use crate::Transport;
    use futures::Future;

    fn contract<T: Transport>(transport: &T) -> Contract<&T> {
        let eth = api::Eth::new(transport);
        Contract::from_json(eth, Address::from_low_u64_be(1), include_bytes!("./res/token.json")).unwrap()
    }

    #[test]
    fn should_call_constant_function() {
        // given
        let mut transport = TestTransport::default();
        transport.set_response(rpc::Value::String("0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c48656c6c6f20576f726c64210000000000000000000000000000000000000000".into()));

        let result: String = {
            let token = contract(&transport);

            // when
            token
                .query("name", (), None, Options::default(), BlockNumber::Number(1))
                .wait()
                .unwrap()
        };

        // then
        transport.assert_request(
            "eth_call",
            &[
                "{\"data\":\"0x06fdde03\",\"to\":\"0x0000000000000000000000000000000000000001\"}".into(),
                "\"0x1\"".into(),
            ],
        );
        transport.assert_no_more_requests();
        assert_eq!(result, "Hello World!".to_owned());
    }

    #[test]
    fn should_query_with_params() {
        // given
        let mut transport = TestTransport::default();
        transport.set_response(rpc::Value::String("0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000c48656c6c6f20576f726c64210000000000000000000000000000000000000000".into()));

        let result: String = {
            let token = contract(&transport);

            // when
            token
                .query(
                    "name",
                    (),
                    Address::from_low_u64_be(5),
                    Options::with(|options| {
                        options.gas_price = Some(10_000_000.into());
                    }),
                    BlockNumber::Latest,
                )
                .wait()
                .unwrap()
        };

        // then
        transport.assert_request("eth_call", &["{\"data\":\"0x06fdde03\",\"from\":\"0x0000000000000000000000000000000000000005\",\"gasPrice\":\"0x989680\",\"to\":\"0x0000000000000000000000000000000000000001\"}".into(), "\"latest\"".into()]);
        transport.assert_no_more_requests();
        assert_eq!(result, "Hello World!".to_owned());
    }

    #[test]
    fn should_call_a_contract_function() {
        // given
        let mut transport = TestTransport::default();
        transport.set_response(rpc::Value::String(format!("{:?}", H256::from_low_u64_be(5))));

        let result = {
            let token = contract(&transport);

            // when
            token
                .call("name", (), Address::from_low_u64_be(5), Options::default())
                .wait()
                .unwrap()
        };

        // then
        transport.assert_request("eth_sendTransaction", &["{\"data\":\"0x06fdde03\",\"from\":\"0x0000000000000000000000000000000000000005\",\"to\":\"0x0000000000000000000000000000000000000001\"}".into()]);
        transport.assert_no_more_requests();
        assert_eq!(result, H256::from_low_u64_be(5));
    }

    #[test]
    fn should_estimate_gas_usage() {
        // given
        let mut transport = TestTransport::default();
        transport.set_response(rpc::Value::String(format!("{:#x}", U256::from(5))));

        let result = {
            let token = contract(&transport);

            // when
            token
                .estimate_gas("name", (), Address::from_low_u64_be(5), Options::default())
                .wait()
                .unwrap()
        };

        // then
        transport.assert_request("eth_estimateGas", &["{\"data\":\"0x06fdde03\",\"from\":\"0x0000000000000000000000000000000000000005\",\"to\":\"0x0000000000000000000000000000000000000001\"}".into(), "\"latest\"".into()]);
        transport.assert_no_more_requests();
        assert_eq!(result, 5.into());
    }

    #[test]
    fn should_query_single_parameter_function() {
        // given
        let mut transport = TestTransport::default();
        transport.set_response(rpc::Value::String(
            "0x0000000000000000000000000000000000000000000000000000000000000020".into(),
        ));

        let result: U256 = {
            let token = contract(&transport);

            // when
            token
                .query("balanceOf", Address::from_low_u64_be(5), None, Options::default(), None)
                .wait()
                .unwrap()
        };

        // then
        transport.assert_request("eth_call", &["{\"data\":\"0x70a082310000000000000000000000000000000000000000000000000000000000000005\",\"to\":\"0x0000000000000000000000000000000000000001\"}".into(), "\"latest\"".into()]);
        transport.assert_no_more_requests();
        assert_eq!(result, 0x20.into());
    }
}
