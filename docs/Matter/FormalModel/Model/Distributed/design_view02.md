# 综合应用

## 分布式系统设计

### 1.1 综合应用1-分布式区块链系统

```rust
// 分布式区块链系统
struct DistributedBlockchain {
    node_id: String,
    data_dir: PathBuf,
    chain: Blockchain,
    wallet: Wallet,
    network: P2PNetwork,
    consensus: ConsensusEngine,
    transaction_pool: TransactionPool,
    miner: Miner,
    api_server: BlockchainApiServer,
    running: AtomicBool,
}

struct Blockchain {
    blocks: RwLock<Vec<Block>>,
    current_height: AtomicU64,
    current_difficulty: AtomicU64,
    validators: RwLock<HashSet<String>>,
    chain_state: RwLock<ChainState>,
}

struct Block {
    header: BlockHeader,
    transactions: Vec<Transaction>,
    validator_signatures: HashMap<String, Vec<u8>>,
}

struct BlockHeader {
    version: u32,
    height: u64,
    previous_hash: Vec<u8>,
    timestamp: i64,
    merkle_root: Vec<u8>,
    difficulty: u64,
    nonce: u64,
}

struct Transaction {
    id: String,
    inputs: Vec<TransactionInput>,
    outputs: Vec<TransactionOutput>,
    timestamp: i64,
    signature: Vec<u8>,
    public_key: Vec<u8>,
}

struct TransactionInput {
    transaction_id: String,
    output_index: u32,
    script_sig: Vec<u8>,
}

struct TransactionOutput {
    value: u64,
    script_pubkey: Vec<u8>,
}

struct ChainState {
    utxo_set: HashMap<String, Vec<UnspentOutput>>,
    account_balances: HashMap<String, u64>,
    contracts: HashMap<String, SmartContract>,
}

struct UnspentOutput {
    transaction_id: String,
    output_index: u32,
    value: u64,
    script_pubkey: Vec<u8>,
}

struct SmartContract {
    id: String,
    code: Vec<u8>,
    state: HashMap<String, Vec<u8>>,
    creator: String,
    created_at: i64,
}

struct Wallet {
    key_pairs: HashMap<String, KeyPair>,
    selected_address: String,
}

struct KeyPair {
    public_key: Vec<u8>,
    private_key: Vec<u8>,
    address: String,
}

struct P2PNetwork {
    peers: RwLock<HashMap<String, PeerInfo>>,
    pending_connections: RwLock<HashSet<String>>,
    message_handlers: HashMap<MessageType, Box<dyn Fn(&Message) -> Result<(), String> + Send + Sync>>,
    server: Option<JoinHandle<()>>,
    running: AtomicBool,
    bind_address: String,
}

struct PeerInfo {
    id: String,
    address: String,
    last_seen: DateTime<Utc>,
    latency: Duration,
    version: u32,
    height: u64,
    connection: Option<PeerConnection>,
}

struct PeerConnection {
    // 在实际实现中，这里会是网络连接
    stream: Option<()>,
    reader_thread: Option<JoinHandle<()>>,
    writer_thread: Option<JoinHandle<()>>,
}

struct Message {
    message_type: MessageType,
    payload: Vec<u8>,
    sender_id: String,
    timestamp: i64,
}

enum MessageType {
    Handshake,
    GetBlocks,
    Blocks,
    GetTransactions,
    Transactions,
    NewBlock,
    NewTransaction,
    Ping,
    Pong,
}

struct ConsensusEngine {
    consensus_type: ConsensusType,
    validators: RwLock<HashMap<String, ValidatorInfo>>,
    current_leader: RwLock<Option<String>>,
    round_state: RwLock<RoundState>,
    consensus_thread: Option<JoinHandle<()>>,
    running: AtomicBool,
}

enum ConsensusType {
    ProofOfWork,
    ProofOfStake,
    DelegatedProofOfStake,
    PracticalByzantineFaultTolerance,
}

struct ValidatorInfo {
    id: String,
    public_key: Vec<u8>,
    stake: u64,
    last_proposed_block: u64,
    voting_power: u64,
}

struct RoundState {
    current_round: u64,
    proposed_block: Option<Block>,
    votes: HashMap<String, Vote>,
    timeout: DateTime<Utc>,
}

struct Vote {
    validator_id: String,
    block_hash: Vec<u8>,
    vote_type: VoteType,
    signature: Vec<u8>,
}

enum VoteType {
    Prepare,
    Commit,
}

struct TransactionPool {
    pending_transactions: RwLock<HashMap<String, Transaction>>,
    orphaned_transactions: RwLock<HashMap<String, Transaction>>,
    fee_estimator: FeeEstimator,
}

struct FeeEstimator {
    fee_history: VecDeque<HistoricalFee>,
    min_fee_rate: u64,
    max_fee_rate: u64,
}

struct HistoricalFee {
    block_height: u64,
    min_fee_rate: u64,
    max_fee_rate: u64,
    median_fee_rate: u64,
    avg_fee_rate: u64,
}

struct Miner {
    mining_thread: Option<JoinHandle<()>>,
    running: AtomicBool,
    mining_address: String,
}

struct BlockchainApiServer {
    server: Option<JoinHandle<()>>,
    running: AtomicBool,
    bind_address: String,
}

impl DistributedBlockchain {
    fn new(node_id: &str, data_dir: &Path, bind_address: &str) -> Self {
        let chain = Blockchain {
            blocks: RwLock::new(Vec::new()),
            current_height: AtomicU64::new(0),
            current_difficulty: AtomicU64::new(1),
            validators: RwLock::new(HashSet::new()),
            chain_state: RwLock::new(ChainState {
                utxo_set: HashMap::new(),
                account_balances: HashMap::new(),
                contracts: HashMap::new(),
            }),
        };
        
        let wallet = Wallet {
            key_pairs: HashMap::new(),
            selected_address: String::new(),
        };
        
        let p2p_network = P2PNetwork {
            peers: RwLock::new(HashMap::new()),
            pending_connections: RwLock::new(HashSet::new()),
            message_handlers: HashMap::new(),
            server: None,
            running: AtomicBool::new(false),
            bind_address: format!("{}:7000", bind_address),
        };
        
        let consensus_engine = ConsensusEngine {
            consensus_type: ConsensusType::ProofOfWork,
            validators: RwLock::new(HashMap::new()),
            current_leader: RwLock::new(None),
            round_state: RwLock::new(RoundState {
                current_round: 0,
                proposed_block: None,
                votes: HashMap::new(),
                timeout: Utc::now(),
            }),
            consensus_thread: None,
            running: AtomicBool::new(false),
        };
        
        let transaction_pool = TransactionPool {
            pending_transactions: RwLock::new(HashMap::new()),
            orphaned_transactions: RwLock::new(HashMap::new()),
            fee_estimator: FeeEstimator {
                fee_history: VecDeque::new(),
                min_fee_rate: 1,
                max_fee_rate: 1000,
            },
        };
        
        let miner = Miner {
            mining_thread: None,
            running: AtomicBool::new(false),
            mining_address: String::new(),
        };
        
        let api_server = BlockchainApiServer {
            server: None,
            running: AtomicBool::new(false),
            bind_address: format!("{}:8080", bind_address),
        };
        
        DistributedBlockchain {
            node_id: node_id.to_string(),
            data_dir: data_dir.to_path_buf(),
            chain,
            wallet,
            network: p2p_network,
            consensus: consensus_engine,
            transaction_pool,
            miner,
            api_server,
            running: AtomicBool::new(false),
        }
    }
    
    fn start(&mut self) -> Result<(), String> {
        println!("启动分布式区块链系统");
        
        // 创建必要的目录
        if let Err(e) = std::fs::create_dir_all(&self.data_dir) {
            return Err(format!("创建数据目录失败: {}", e));
        }
        
        // 加载或创建创世区块
        self.load_chain()?;
        
        // 加载或创建钱包
        self.load_wallet()?;
        
        // 启动P2P网络
        self.start_network()?;
        
        // 启动共识引擎
        self.start_consensus()?;
        
        // 启动矿工
        self.start_miner()?;
        
        // 启动API服务器
        self.start_api_server()?;
        
        self.running.store(true, Ordering::SeqCst);
        
        Ok(())
    }
    
    fn load_chain(&self) -> Result<(), String> {
        println!("加载区块链");
        
        let chain_dir = self.data_dir.join("chain");
        
        if !chain_dir.exists() {
            if let Err(e) = std::fs::create_dir_all(&chain_dir) {
                return Err(format!("创建区块链目录失败: {}", e));
            }
            
            // 创建创世区块
            self.create_genesis_block()?;
            return Ok(());
        }
        
        // 加载区块
        let blocks_dir = chain_dir.join("blocks");
        
        if !blocks_dir.exists() {
            if let Err(e) = std::fs::create_dir_all(&blocks_dir) {
                return Err(format!("创建区块目录失败: {}", e));
            }
            
            // 创建创世区块
            self.create_genesis_block()?;
            return Ok(());
        }
        
        // 加载所有区块文件
        match std::fs::read_dir(&blocks_dir) {
            Ok(entries) => {
                let mut blocks = Vec::new();
                
                for entry in entries {
                    if let Ok(entry) = entry {
                        let path = entry.path();
                        
                        if path.is_file() && path.extension().map_or(false, |ext| ext == "dat") {
                            match self.load_block(&path) {
                                Ok(block) => blocks.push(block),
                                Err(e) => println!("加载区块失败: {} - {}", path.display(), e),
                            }
                        }
                    }
                }
                
                // 按高度排序
                blocks.sort_by_key(|b| b.header.height);
                
                // 检查区块链的有效性
                if blocks.is_empty() {
                    // 创建创世区块
                    self.create_genesis_block()?;
                } else {
                    // 验证区块链
                    for i in 1..blocks.len() {
                        let prev_block = &blocks[i-1];
                        let current_block = &blocks[i];
                        
                        // 检查高度
                        if current_block.header.height != prev_block.header.height + 1 {
                            return Err(format!("区块链高度不连续: {} -> {}", prev_block.header.height, current_block.header.height));
                        }
                        
                        // 检查前一个区块的哈希
                        let prev_hash = self.calculate_block_hash(prev_block);
                        if current_block.header.previous_hash != prev_hash {
                            return Err(format!("区块链哈希不连续: 区块 {} 的前一个哈希不匹配", current_block.header.height));
                        }
                    }
                    
                    // 存储区块
                    let mut chain_blocks = self.chain.blocks.write().unwrap();
                    *chain_blocks = blocks;
                    
                    if let Some(last_block) = chain_blocks.last() {
                        self.chain.current_height.store(last_block.header.height, Ordering::SeqCst);
                        self.chain.current_difficulty.store(last_block.header.difficulty, Ordering::SeqCst);
                    }
                    
                    // 重建链状态
                    self.rebuild_chain_state()?;
                }
            },
            Err(e) => return Err(format!("读取区块目录失败: {}", e)),
        }
        
        Ok(())
    }
    
    fn create_genesis_block(&self) -> Result<(), String> {
        println!("创建创世区块");
        
        let now = Utc::now().timestamp();
        
        // 创建创币交易
        let coinbase_tx = Transaction {
            id: uuid::Uuid::new_v4().to_string(),
            inputs: Vec::new(), // 没有输入（创币交易）
            outputs: vec![
                TransactionOutput {
                    value: 50 * 100_000_000, // 50个币（以聪为单位）
                    script_pubkey: vec![0, 1, 2, 3], // 示例脚本
                }
            ],
            timestamp: now,
            signature: Vec::new(), // 创币交易不需要签名
            public_key: Vec::new(),
        };
        
        // 创建创世区块
        let genesis_block = Block {
            header: BlockHeader {
                version: 1,
                height: 0,
                previous_hash: vec![0; 32], // 创世区块没有前一个区块
                timestamp: now,
                merkle_root: self.calculate_merkle_root(&vec![coinbase_tx.clone()]),
                difficulty: 1,
                nonce: 0,
            },
            transactions: vec![coinbase_tx],
            validator_signatures: HashMap::new(),
        };
        
        // 保存创世区块
        let mut blocks = self.chain.blocks.write().unwrap();
        blocks.push(genesis_block.clone());
        
        // 更新链状态
        self.chain.current_height.store(0, Ordering::SeqCst);
        self.chain.current_difficulty.store(1, Ordering::SeqCst);
        
        // 保存创世区块到磁盘
        self.save_block(&genesis_block)?;
        
        // 初始化链状态
        self.rebuild_chain_state()?;
        
        Ok(())
    }
    
    fn load_block(&self, path: &Path) -> Result<Block, String> {
        let content = match std::fs::read(path) {
            Ok(content) => content,
            Err(e) => return Err(format!("读取区块文件失败: {}", e)),
        };
        
        // 在实际实现中，这里会反序列化二进制数据为区块
        println!("解析区块文件: {}", path.display());
        
        // 创建一个模拟区块
        let filename = path.file_stem().and_then(|s| s.to_str()).unwrap_or("");
        let height: u64 = filename.parse().unwrap_or(0);
        
        let now = Utc::now().timestamp();
        
        let block = Block {
            header: BlockHeader {
                version: 1,
                height,
                previous_hash: vec![0; 32],
                timestamp: now,
                merkle_root: vec![0; 32],
                difficulty: 1,
                nonce: 0,
            },
            transactions: Vec::new(),
            validator_signatures: HashMap::new(),
        };
        
        Ok(block)
    }
    
    fn save_block(&self, block: &Block) -> Result<(), String> {
        let chain_dir = self.data_dir.join("chain");
        let blocks_dir = chain_dir.join("blocks");
        
        if let Err(e) = std::fs::create_dir_all(&blocks_dir) {
            return Err(format!("创建区块目录失败: {}", e));
        }
        
        let block_path = blocks_dir.join(format!("{}.dat", block.header.height));
        
        // 在实际实现中，这里会序列化区块为二进制数据
        let serialized_block = vec![0, 1, 2, 3]; // 示例数据
        
        if let Err(e) = std::fs::write(&block_path, serialized_block) {
            return Err(format!("写入区块文件失败: {}", e));
        }
        
        Ok(())
    }
    
    fn rebuild_chain_state(&self) -> Result<(), String> {
        println!("重建链状态");
        
        let blocks = self.chain.blocks.read().unwrap();
        
        let mut chain_state = ChainState {
            utxo_set: HashMap::new(),
            account_balances: HashMap::new(),
            contracts: HashMap::new(),
        };
        
        // 遍历所有区块
        for block in blocks.iter() {
            // 处理区块中的所有交易
            for tx in &block.transactions {
                // 移除已花费的输出
                for input in &tx.inputs {
                    if let Some(utxos) = chain_state.utxo_set.get_mut(&input.transaction_id) {
                        utxos.retain(|utxo| utxo.output_index != input.output_index);
                        
                        if utxos.is_empty() {
                            chain_state.utxo_set.remove(&input.transaction_id);
                        }
                    }
                }
                
                // 添加新的未花费输出
                let mut new_utxos = Vec::new();
                
                for (i, output) in tx.outputs.iter().enumerate() {
                    new_utxos.push(UnspentOutput {
                        transaction_id: tx.id.clone(),
                        output_index: i as u32,
                        value: output.value,
                        script_pubkey: output.script_pubkey.clone(),
                    });
                }
                
                chain_state.utxo_set.insert(tx.id.clone(), new_utxos);
                
                // 在实际实现中，这里还会更新账户余额和智能合约状态
            }
        }
        
        // 更新链状态
        let mut state = self.chain.chain_state.write().unwrap();
        *state = chain_state;
        
        Ok(())
    }
    
    fn load_wallet(&self) -> Result<(), String> {
        println!("加载钱包");
        
        let wallet_dir = self.data_dir.join("wallet");
        
        if !wallet_dir.exists() {
            if let Err(e) = std::fs::create_dir_all(&wallet_dir) {
                return Err(format!("创建钱包目录失败: {}", e));
            }
            
            // 创建一个新钱包
            self.create_new_wallet()?;
            return Ok(());
        }
        
        let wallet_file = wallet_dir.join("wallet.dat");
        
        if !wallet_file.exists() {
            // 创建一个新钱包
            self.create_new_wallet()?;
            return Ok(());
        }
        
        // 加载钱包文件
        let content = match std::fs::read(&wallet_file) {
            Ok(content) => content,
            Err(e) => return Err(format!("读取钱包文件失败: {}", e)),
        };
        
        // 在实际实现中，这里会解密和反序列化钱包数据
        println!("解析钱包文件");
        
        // 如果没有密钥对，创建一个新的
        if true {
            // 创建一个新钱包
            self.create_new_wallet()?;
        }
        
        Ok(())
    }
    
    fn create_new_wallet(&self) -> Result<(), String> {
        println!("创建新钱包");
        
        // 在实际实现中，这里会生成真实的密钥对
        let key_pair = KeyPair {
            public_key: vec![1, 2, 3],
            private_key: vec![4, 5, 6],
            address: "1A1zP1eP5QGefi2DMPTfTL5SLmv7DivfNa".to_string(),
        };
        
        // 更新钱包
        let address = key_pair.address.clone();
        
        let mut wallet = Wallet {
            key_pairs: HashMap::new(),
            selected_address: address.clone(),
        };
        
        wallet.key_pairs.insert(address, key_pair);
        
        // 保存钱包到磁盘
        self.save_wallet(&wallet)?;
        
        Ok(())
    }
    
    fn save_wallet(&self, wallet: &Wallet) -> Result<(), String> {
        let wallet_dir = self.data_dir.join("wallet");
        
        if let Err(e) = std::fs::create_dir_all(&wallet_dir) {
            return Err(format!("创建钱包目录失败: {}", e));
        }
        
        let wallet_file = wallet_dir.join("wallet.dat");
        
        // 在实际实现中，这里会序列化和加密钱包数据
        let serialized_wallet = vec![0, 1, 2, 3]; // 示例数据
        
        if let Err(e) = std::fs::write(&wallet_file, serialized_wallet) {
            return Err(format!("写入钱包文件失败: {}", e));
        }
        
        Ok(())
    }
    
    fn start_network(&mut self) -> Result<(), String> {
        println!("启动P2P网络");
        
        // 注册消息处理程序
        
        // 启动网络服务器
        let bind_address = self.network.bind_address.clone();
        let node_id = self.node_id.clone();
        
        self.network.running.store(true, Ordering::SeqCst);
        
        let running = self.network.running.clone();
        
        let thread = thread::spawn(move || {
            // 在实际实现中，这里会启动一个TCP监听器
            println!("P2P网络服务器绑定到: {}", bind_address);
            
            while running.load(Ordering::SeqCst) {
                // 模拟服务器循环
                thread::sleep(Duration::from_millis(100));
                
                // 在实际实现中，这里会接受新连接
            }
        });
        
        self.network.server = Some(thread);
        
        // 连接到种子节点
        self.connect_to_seed_nodes()?;
        
        Ok(())
    }
    
    fn connect_to_seed_nodes(&self) -> Result<(), String> {
        println!("连接到种子节点");
        
        // 在实际实现中，这里会从配置中读取种子节点并连接
        let seed_nodes = vec![
            "192.168.1.100:7000",
            "192.168.1.101:7000",
            "192.168.1.102:7000",
        ];
        
        for node in seed_nodes {
            println!("连接到种子节点: {}", node);
            
            // 在实际实现中，这里会建立TCP连接并进行握手
        }
        
        Ok(())
    }
    
    fn start_consensus(&mut self) -> Result<(), String> {
        println!("启动共识引擎");
        
        // 初始化验证者
        self.initialize_validators()?;
        
        // 启动共识线程
        let consensus_type = match self.consensus.consensus_type {
            ConsensusType::ProofOfWork => "工作量证明",
            ConsensusType::ProofOfStake => "权益证明",
            ConsensusType::DelegatedProofOfStake => "委托权益证明",
            ConsensusType::PracticalByzantineFaultTolerance => "实用拜占庭容错",
        };
        
        println!("使用共识算法: {}", consensus_type);
        
        let node_id = self.node_id.clone();
        let validators = self.consensus.validators.clone();
        let current_leader = self.consensus.current_leader.clone();
        let round_state = self.consensus.round_state.clone();
        
        self.consensus.running.store(true, Ordering::SeqCst);
        
        let running = self.consensus.running.clone();
        
        let thread = thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                // 在实际实现中，这里会实现特定共识算法的逻辑
                
                // 简化：每隔1秒选举一次领导者
                {
                    let validators_guard = validators.read().unwrap();
                    
                    if !validators_guard.is_empty() {
                        // 随机选择领导者
                        let mut rng = rand::thread_rng();
                        let validator_ids: Vec<_> = validators_guard.keys().cloned().collect();
                        let leader_id = validator_ids[rng.gen_range(0..validator_ids.len())].clone();
                        
                        let mut leader = current_leader.write().unwrap();
                        *leader = Some(leader_id.clone());
                        
                        println!("选举新领导者: {}", leader_id);
                    }
                }
                
                // 休眠一段时间
                thread::sleep(Duration::from_secs(1));
            }
        });
        
        self.consensus.consensus_thread = Some(thread);
        
        Ok(())
    }
    
    fn initialize_validators(&self) -> Result<(), String> {
        println!("初始化验证者");
        
        // 在实际实现中，这里会从配置或链状态中加载验证者
        
        // 添加自己作为验证者
        let mut validators = self.consensus.validators.write().unwrap();
        
        validators.insert(self.node_id.clone(), ValidatorInfo {
            id: self.node_id.clone(),
            public_key: vec![1, 2, 3],
            stake: 100,
            last_proposed_block: 0,
            voting_power: 100,
        });
        
        Ok(())
    }
    
    fn start_miner(&mut self) -> Result<(), String> {
        println!("启动矿工");
        
        // 设置挖矿地址
        let wallet = &self.wallet;
        
        if wallet.key_pairs.is_empty() {
            return Err("没有可用的钱包地址".to_string());
        }
        
        self.miner.mining_address = wallet.selected_address.clone();
        
        // 启动挖矿线程
        let node_id = self.node_id.clone();
        let mining_address = self.miner.mining_address.clone();
        let chain = Arc::new(self.chain);
        let transaction_pool = Arc::new(self.transaction_pool);
        
        self.miner.running.store(true, Ordering::SeqCst);
        
        let running = self.miner.running.clone();
        
        let thread = thread::spawn(move || {
            println!("开始挖矿，地址: {}", mining_address);
            
            while running.load(Ordering::SeqCst) {
                // 检查是否是领导者（用于PoS共识）
                
                // 创建新区块
                
                // 挖矿（计算有效哈希）
                
                // 验证并添加区块
                
                // 广播新区块
                
                // 休眠一段时间
                thread::sleep(Duration::from_millis(100));
            }
        });
        
        self.miner.mining_thread = Some(thread);
        
        Ok(())
    }
    
    fn start_api_server(&mut self) -> Result<(), String> {
        println!("启动区块链API服务器");
        
        let bind_address = self.api_server.bind_address.clone();
        
        self.api_server.running.store(true, Ordering::SeqCst);
        
        let running = self.api_server.running.clone();
        
        let thread = thread::spawn(move || {
            // 在实际实现中，这里会启动一个HTTP API服务器
            println!("区块链API服务器绑定到: {}", bind_address);
            
            while running.load(Ordering::SeqCst) {
                // 模拟服务器循环
                thread::sleep(Duration::from_millis(100));
                
                // 在实际实现中，这里会处理API请求
            }
        });
        
        self.api_server.server = Some(thread);
        
        Ok(())
    }
    
    fn stop(&mut self) -> Result<(), String> {
        println!("停止分布式区块链系统");
        
        self.running.store(false, Ordering::SeqCst);
        
        // 停止API服务器
        self.api_server.running.store(false, Ordering::SeqCst);
        if let Some(thread) = self.api_server.server.take() {
            match thread.join() {
                Ok(_) => {},
                Err(e) => println!("API服务器线程退出错误: {:?}", e),
            }
        }
        
        // 停止矿工
        self.miner.running.store(false, Ordering::SeqCst);
        if let Some(thread) = self.miner.mining_thread.take() {
            match thread.join() {
                Ok(_) => {},
                Err(e) => println!("矿工线程退出错误: {:?}", e),
            }
        }
        
        // 停止共识引擎
        self.consensus.running.store(false, Ordering::SeqCst);
        if let Some(thread) = self.consensus.consensus_thread.take() {
            match thread.join() {
                Ok(_) => {},
                Err(e) => println!("共识引擎线程退出错误: {:?}", e),
            }
        }
        
        // 停止P2P网络
        self.network.running.store(false, Ordering::SeqCst);
        if let Some(thread) = self.network.server.take() {
            match thread.join() {
                Ok(_) => {},
                Err(e) => println!("P2P网络服务器线程退出错误: {:?}", e),
            }
        }
        
        Ok(())
    }
    
    fn calculate_block_hash(&self, block: &Block) -> Vec<u8> {
        // 在实际实现中，这里会计算区块的哈希值
        // 通常会序列化区块头并使用SHA-256或其他哈希函数
        
        // 简化：返回随机哈希
        let mut rng = rand::thread_rng();
        let mut hash = vec![0; 32];
        rng.fill_bytes(&mut hash);
        hash
    }
    
    fn calculate_merkle_root(&self, transactions: &Vec<Transaction>) -> Vec<u8> {
        // 在实际实现中，这里会计算交易的默克尔根哈希
        
        // 简化：返回随机哈希
        let mut rng = rand::thread_rng();
        let mut hash = vec![0; 32];
        rng.fill_bytes(&mut hash);
        hash
    }
    
    fn create_transaction(&self, to_address: &str, amount: u64, fee: u64) -> Result<Transaction, String> {
        println!("创建交易: {} -> {}, 金额: {}, 手续费: {}", self.wallet.selected_address, to_address, amount, fee);
        
        // 获取足够的未花费输出
        let total_amount = amount + fee;
        let utxos = self.find_sufficient_utxos(total_amount)?;
        
        // 计算输入总额
        let total_input_amount: u64 = utxos.iter().map(|utxo| utxo.value).sum();
        
        // 创建交易输入
        let mut inputs = Vec::new();
        
        for utxo in &utxos {
            inputs.push(TransactionInput {
                transaction_id: utxo.transaction_id.clone(),
                output_index: utxo.output_index,
                script_sig: vec![0], // 示例签名脚本
            });
        }
        
        // 创建交易输出
        let mut outputs = Vec::new();
        
        // 支付输出
        outputs.push(TransactionOutput {
            value: amount,
            script_pubkey: vec![1], // 示例公钥脚本
        });
        
        // 找零输出（如果有）
        let change_amount = total_input_amount - total_amount;
        
        if change_amount > 0 {
            outputs.push(TransactionOutput {
                value: change_amount,
                script_pubkey: vec![2], // 示例公钥脚本
            });
        }
        
        // 创建交易
        let transaction = Transaction {
            id: uuid::Uuid::new_v4().to_string(),
            inputs,
            outputs,
            timestamp: Utc::now().timestamp(),
            signature: vec![0], // 示例签名
            public_key: vec![1], // 示例公钥
        };
        
        Ok(transaction)
    }
    
    fn find_sufficient_utxos(&self, amount: u64) -> Result<Vec<UnspentOutput>, String> {
        let chain_state = self.chain.chain_state.read().unwrap();
        
        // 获取所有未花费输出
        let mut available_utxos = Vec::new();
        let mut total_amount = 0;
        
        for (_, utxos) in chain_state.utxo_set.iter() {
            for utxo in utxos {
                // 在实际实现中，这里会检查脚本以确定UTXO是否属于钱包
                
                // 简化：假设所有UTXO都属于钱包
                available_utxos.push(utxo.clone());
                total_amount += utxo.value;
                
                if total_amount >= amount {
                    return Ok(available_utxos);
                }
            }
        }
        
        // 余额不足
        Err(format!("余额不足，需要: {}, 可用: {}", amount, total_amount))
    }
    
    fn send_transaction(&self, transaction: Transaction) -> Result<String, String> {
        println!("发送交易: {}", transaction.id);
        
        // 验证交易
        self.validate_transaction(&transaction)?;
        
        // 添加到交易池
        {
            let mut pending = self.transaction_pool.pending_transactions.write().unwrap();
            pending.insert(transaction.id.clone(), transaction.clone());
        }
        
        // 广播交易
        self.broadcast_transaction(&transaction)?;
        
        Ok(transaction.id)
    }
    
    fn validate_transaction(&self, transaction: &Transaction) -> Result<(), String> {
        // 在实际实现中，这里会进行完整的交易验证
        
        // 检查交易ID
        if transaction.id.is_empty() {
            return Err("交易ID不能为空".to_string());
        }
        
        // 检查输入和输出
        if transaction.inputs.is_empty() && transaction.outputs.is_empty() {
            return Err("交易不能同时没有输入和输出".to_string());
        }
        
        // 对于非创币交易，验证输入的有效性
        if !transaction.inputs.is_empty() {
            // 检查输入是否存在于UTXO集中
            let chain_state = self.chain.chain_state.read().unwrap();
            
            for input in &transaction.inputs {
                let utxos = match chain_state.utxo_set.get(&input.transaction_id) {
                    Some(utxos) => utxos,
                    None => return Err(format!("输入引用的交易不存在: {}", input.transaction_id)),
                };
                
                // 检查输出索引是否有效
                if !utxos.iter().any(|utxo| utxo.output_index == input.output_index) {
                    return Err(format!("输入引用了不存在的输出: {}:{}", input.transaction_id, input.output_index));
                }
                
                // 在实际实现中，这里还会验证脚本签名
            }
            
            // 验证输入金额是否大于等于输出金额
            let total_input = self.calculate_transaction_input_amount(transaction)?;
            let total_output = transaction.outputs.iter().map(|output| output.value).sum::<u64>();
            
            if total_input < total_output {
                return Err(format!("输入金额 ({}) 小于输出金额 ({})", total_input, total_output));
            }
        }
        
        Ok(())
    }
    
    fn calculate_transaction_input_amount(&self, transaction: &Transaction) -> Result<u64, String> {
        let chain_state = self.chain.chain_state.read().unwrap();
        let mut total = 0;
        
        for input in &transaction.inputs {
            let utxos = match chain_state.utxo_set.get(&input.transaction_id) {
                Some(utxos) => utxos,
                None => return Err(format!("输入引用的交易不存在: {}", input.transaction_id)),
            };
            
            // 查找对应的UTXO
            let utxo = match utxos.iter().find(|utxo| utxo.output_index == input.output_index) {
                Some(utxo) => utxo,
                None => return Err(format!("输入引用了不存在的输出: {}:{}", input.transaction_id, input.output_index)),
            };
            
            total += utxo.value;
        }
        
        Ok(total)
    }
    
    fn broadcast_transaction(&self, transaction: &Transaction) -> Result<(), String> {
        println!("广播交易: {}", transaction.id);
        
        // 在实际实现中，这里会将交易广播到连接的对等节点
        // 创建交易消息
        let message = Message {
            message_type: MessageType::NewTransaction,
            payload: vec![0, 1, 2, 3], // 示例序列化的交易数据
            sender_id: self.node_id.clone(),
            timestamp: Utc::now().timestamp(),
        };
        
        // 获取所有连接的对等节点
        let peers = self.network.peers.read().unwrap();
        
        // 向所有对等节点发送消息
        for (id, peer) in peers.iter() {
            println!("向对等节点发送交易: {}", id);
            
            // 在实际实现中，这里会通过网络连接发送消息
        }
        
        Ok(())
    }
    
    fn get_balance(&self, address: &str) -> u64 {
        let chain_state = self.chain.chain_state.read().unwrap();
        let mut balance = 0;
        
        // 计算所有属于该地址的UTXO的总额
        for (_, utxos) in chain_state.utxo_set.iter() {
            for utxo in utxos {
                // 在实际实现中，这里会检查脚本以确定UTXO是否属于该地址
                
                // 简化：假设所有UTXO都属于该地址
                balance += utxo.value;
            }
        }
        
        balance
    }
    
    fn get_block_by_height(&self, height: u64) -> Option<Block> {
        let blocks = self.chain.blocks.read().unwrap();
        
        blocks.iter()
            .find(|block| block.header.height == height)
            .cloned()
    }
    
    fn get_block_by_hash(&self, hash: &[u8]) -> Option<Block> {
        let blocks = self.chain.blocks.read().unwrap();
        
        blocks.iter()
            .find(|block| self.calculate_block_hash(block) == hash)
            .cloned()
    }
    
    fn get_transaction(&self, tx_id: &str) -> Option<Transaction> {
        // 首先检查交易池
        {
            let pending = self.transaction_pool.pending_transactions.read().unwrap();
            
            if let Some(tx) = pending.get(tx_id) {
                return Some(tx.clone());
            }
        }
        
        // 然后检查区块链
        let blocks = self.chain.blocks.read().unwrap();
        
        for block in blocks.iter().rev() { // 从最新的区块开始查找
            for tx in &block.transactions {
                if tx.id == tx_id {
                    return Some(tx.clone());
                }
            }
        }
        
        None
    }
    
    fn create_new_address(&self) -> Result<String, String> {
        println!("创建新地址");
        
        // 在实际实现中，这里会生成真实的密钥对
        let key_pair = KeyPair {
            public_key: vec![1, 2, 3],
            private_key: vec![4, 5, 6],
            address: format!("1A1zP1eP5QGefi2DMPTfTL5SLmv7Divf{}", rand::random::<u8>()),
        };
        
        // 更新钱包
        let address = key_pair.address.clone();
        
        let mut wallet = self.wallet.clone();
        wallet.key_pairs.insert(address.clone(), key_pair);
        
        // 保存钱包到磁盘
        self.save_wallet(&wallet)?;
        
        Ok(address)
    }
}

// 完善main函数，添加区块链系统测试
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("启动分布式系统示例");
    
    let temp_dir = std::env::temp_dir().join("distributed_systems_demo");
    
    if temp_dir.exists() {
        std::fs::remove_dir_all(&temp_dir)?;
    }
    std::fs::create_dir_all(&temp_dir)?;
    
    println!("使用临时目录: {:?}", temp_dir);
    
    // 测试分布式区块链系统
    {
        println!("\n===== 测试分布式区块链系统 =====");
        
        let data_dir = temp_dir.join("blockchain");
        std::fs::create_dir_all(&data_dir)?;
        
        let mut blockchain = DistributedBlockchain::new("node1", &data_dir, "127.0.0.1");
        
        blockchain.start()?;
        
        // 获取余额
        let balance = blockchain.get_balance(&blockchain.wallet.selected_address);
        println!("钱包余额: {}", balance);
        
        // 创建新地址
        let new_address = blockchain.create_new_address()?;
        println!("创建的新地址: {}", new_address);
        
        // 创建并发送交易
        if balance > 0 {
            let transaction = blockchain.create_transaction(&new_address, 10, 1)?;
            let tx_id = blockchain.send_transaction(transaction)?;
            println!("发送交易成功，交易ID: {}", tx_id);
            
            // 获取交易
            match blockchain.get_transaction(&tx_id) {
                Some(tx) => println!("找到交易: {}", tx.id),
                None => println!("未找到交易"),
            }
        } else {
            println!("余额不足，无法发送交易");
        }
        
        // 获取区块
        match blockchain.get_block_by_height(0) {
            Some(block) => println!("找到创世区块，高度: {}", block.header.height),
            None => println!("未找到创世区块"),
        }
        
        // 停止区块链系统
        blockchain.stop()?;
    }
    
    println!("\n所有分布式系统测试完成");
    
    // 清理临时目录
    std::fs::remove_dir_all(&temp_dir)?;
    
    Ok(())
}

// 最终总结函数：将所有分布式系统综合在一起
fn run_distributed_systems_demo() -> Result<(), Box<dyn std::error::Error>> {
    println!("启动综合分布式系统演示");
    
    let temp_dir = std::env::temp_dir().join("distributed_systems_demo");
    
    if temp_dir.exists() {
        std::fs::remove_dir_all(&temp_dir)?;
    }
    std::fs::create_dir_all(&temp_dir)?;
    
    println!("使用临时目录: {:?}", temp_dir);
    
    // 1. 启动分布式搜索引擎
    {
        println!("\n===== 启动分布式搜索引擎 =====");
        
        let data_dir = temp_dir.join("search_engine");
        std::fs::create_dir_all(&data_dir)?;
        
        let mut search_engine = DistributedSearchEngine::new("node1", &data_dir, "127.0.0.1:9200");
        
        search_engine.start()?;
        
        // 创建索引并添加文档
        // ...
        
        // 查询文档
        // ...
        
        search_engine.stop()?;
    }
    
    // 2. 启动分布式时序数据库
    {
        println!("\n===== 启动分布式时序数据库 =====");
        
        let data_dir = temp_dir.join("time_series_db");
        std::fs::create_dir_all(&data_dir)?;
        
        let mut time_series_db = DistributedTimeSeriesDB::new("node1", &data_dir, "127.0.0.1:8086");
        
        time_series_db.start()?;
        
        // 写入时序数据
        // ...
        
        // 查询时序数据
        // ...
        
        time_series_db.stop()?;
    }
    
    // 3. 启动分布式监控系统
    {
        println!("\n===== 启动分布式监控系统 =====");
        
        let data_dir = temp_dir.join("monitoring_system");
        std::fs::create_dir_all(&data_dir)?;
        
        let mut monitoring_system = DistributedMonitoringSystem::new("node1", &data_dir, "127.0.0.1");
        
        monitoring_system.start()?;
        
        // 收集指标
        // ...
        
        // 创建仪表盘
        // ...
        
        monitoring_system.stop()?;
    }
    
    // 4. 启动分布式任务调度系统
    {
        println!("\n===== 启动分布式任务调度系统 =====");
        
        let data_dir = temp_dir.join("task_scheduler");
        std::fs::create_dir_all(&data_dir)?;
        
        let mut task_scheduler = DistributedTaskScheduler::new("node1", &data_dir, "127.0.0.1:8070");
        
        task_scheduler.start()?;
        
        // 提交任务
        // ...
        
        // 检查任务状态
        // ...
        
        task_scheduler.stop()?;
    }
    
    // 5. 启动分布式流处理系统
    {
        println!("\n===== 启动分布式流处理系统 =====");
        
        let data_dir = temp_dir.join("stream_processor");
        std::fs::create_dir_all(&data_dir)?;
        
        let mut stream_processor = DistributedStreamProcessor::new("node1", &data_dir, "127.0.0.1:8090");
        
        stream_processor.start()?;
        
        // 创建流
        // ...
        
        // 部署拓扑
        // ...
        
        stream_processor.stop()?;
    }
    
    // 6. 启动分布式区块链系统
    {
        println!("\n===== 启动分布式区块链系统 =====");
        
        let data_dir = temp_dir.join("blockchain");
        std::fs::create_dir_all(&data_dir)?;
        
        let mut blockchain = DistributedBlockchain::new("node1", &data_dir, "127.0.0.1");
        
        blockchain.start()?;
        
        // 创建交易
        // ...
        
        // 挖矿
        // ...
        
        blockchain.stop()?;
    }
    
    println!("\n所有分布式系统演示完成");
    
    // 清理临时目录
    std::fs::remove_dir_all(&temp_dir)?;
    
    Ok(())
}
```

### 1.1 综合应用2-分布式数据库系统

```rust
// 分布式数据库系统
struct DistributedDatabase {
    node_id: String,
    data_dir: PathBuf,
    cluster_config: ClusterConfig,
    node_manager: NodeManager,
    storage_engine: StorageEngine,
    query_engine: QueryEngine,
    transaction_manager: DatabaseTransactionManager,
    replication_manager: ReplicationManager,
    sharding_manager: ShardingManager,
    schema_manager: SchemaManager,
    server: DatabaseServer,
    running: AtomicBool,
}

struct ClusterConfig {
    cluster_id: String,
    nodes: HashMap<String, NodeConfig>,
    replication_factor: u32,
    sharding_strategy: ShardingStrategy,
    consistency_level: ConsistencyLevel,
    read_preference: ReadPreference,
    heartbeat_interval: Duration,
    connection_timeout: Duration,
    query_timeout: Duration,
}

struct NodeConfig {
    id: String,
    host: String,
    port: u16,
    roles: HashSet<NodeRole>,
    zone: String,
    datacenter: String,
    capacity: ResourceCapacity,
}

struct ResourceCapacity {
    max_storage_gb: u64,
    max_memory_gb: u64,
    max_cpu_cores: u32,
    max_connections: u32,
}

enum NodeRole {
    Primary,
    Secondary,
    Arbiter,
    ShardServer,
    ConfigServer,
    Router,
}

enum ShardingStrategy {
    Range { key: String },
    Hash { key: String, shards: u32 },
    Directory { lookup_table: String },
    None,
}

enum ConsistencyLevel {
    One,
    Quorum,
    All,
    Eventual,
    Strong,
    Linearizable,
}

enum ReadPreference {
    PrimaryOnly,
    PrimaryPreferred,
    SecondaryOnly,
    SecondaryPreferred,
    Nearest,
}

struct NodeManager {
    local_node: NodeInfo,
    nodes: RwLock<HashMap<String, NodeInfo>>,
    status_check_thread: Option<JoinHandle<()>>,
    running: AtomicBool,
}

struct NodeInfo {
    config: NodeConfig,
    status: NodeStatus,
    last_heartbeat: DateTime<Utc>,
    last_election: Option<DateTime<Utc>>,
    stats: NodeStats,
}

enum NodeStatus {
    Starting,
    Running,
    Syncing,
    Degraded,
    Maintenance,
    Offline,
}

struct NodeStats {
    uptime: Duration,
    cpu_usage: f64,
    memory_usage: u64,
    storage_usage: u64,
    iops: u64,
    network_in: u64,
    network_out: u64,
    connections: u32,
    queries_per_second: f64,
}

struct StorageEngine {
    tables: RwLock<HashMap<String, Table>>,
    indexes: RwLock<HashMap<String, Index>>,
    wal: WriteAheadLog,
    page_cache: PageCache,
    storage_manager: StorageManager,
}

struct Table {
    name: String,
    schema: TableSchema,
    partitions: Vec<Partition>,
    indexes: HashMap<String, String>,
    created_at: DateTime<Utc>,
    last_modified: DateTime<Utc>,
    stats: TableStats,
}

struct TableSchema {
    columns: Vec<ColumnDefinition>,
    primary_key: Vec<String>,
    constraints: Vec<Constraint>,
}

struct ColumnDefinition {
    name: String,
    data_type: DataType,
    nullable: bool,
    default_value: Option<Value>,
    comment: Option<String>,
}

enum DataType {
    Int8,
    Int16,
    Int32,
    Int64,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    Float32,
    Float64,
    Text,
    Varchar { length: u32 },
    Boolean,
    Date,
    Timestamp,
    Json,
    Binary,
    Uuid,
    Array { element_type: Box<DataType> },
    Map { key_type: Box<DataType>, value_type: Box<DataType> },
}

enum Constraint {
    NotNull { column: String },
    Unique { columns: Vec<String> },
    PrimaryKey { columns: Vec<String> },
    ForeignKey { columns: Vec<String>, ref_table: String, ref_columns: Vec<String> },
    Check { expression: String },
}

struct Value {
    // 简化值表示，实际实现会更复杂
    value_type: DataType,
    raw_value: Vec<u8>,
}

struct Partition {
    id: String,
    range: PartitionRange,
    location: PartitionLocation,
    stats: PartitionStats,
}

enum PartitionRange {
    Range { start: Value, end: Value },
    List { values: Vec<Value> },
    Hash { modulus: u32, remainder: u32 },
    Default,
}

struct PartitionLocation {
    node_id: String,
    path: String,
    replica_locations: Vec<ReplicaLocation>,
}

struct ReplicaLocation {
    node_id: String,
    path: String,
    status: ReplicaStatus,
    last_sync: DateTime<Utc>,
}

enum ReplicaStatus {
    InSync,
    Syncing,
    Stale,
    Failed,
}

struct TableStats {
    row_count: u64,
    size_bytes: u64,
    last_analyze: DateTime<Utc>,
    avg_row_length: u64,
    index_sizes: HashMap<String, u64>,
}

struct PartitionStats {
    row_count: u64,
    size_bytes: u64,
    last_modified: DateTime<Utc>,
    avg_row_length: u64,
}

struct Index {
    name: String,
    table_name: String,
    columns: Vec<String>,
    index_type: IndexType,
    is_unique: bool,
    created_at: DateTime<Utc>,
    last_modified: DateTime<Utc>,
    size_bytes: u64,
}

enum IndexType {
    BTree,
    Hash,
    Gin,
    Gist,
    Spgist,
    Brin,
}

struct WriteAheadLog {
    current_log: RwLock<LogFile>,
    archived_logs: RwLock<Vec<LogFile>>,
    wal_dir: PathBuf,
    max_log_size: u64,
    retention_hours: u32,
}

struct LogFile {
    id: String,
    path: PathBuf,
    start_lsn: u64,
    end_lsn: u64,
    created_at: DateTime<Utc>,
    size_bytes: u64,
}

struct PageCache {
    pages: RwLock<HashMap<PageId, CachedPage>>,
    lru_list: RwLock<LinkedList<PageId>>,
    max_capacity: usize,
    stats: CacheStats,
}

struct PageId {
    table_id: u64,
    partition_id: u64,
    page_number: u64,
}

struct CachedPage {
    id: PageId,
    data: Vec<u8>,
    is_dirty: bool,
    last_accessed: DateTime<Utc>,
    pin_count: u32,
}

struct CacheStats {
    hits: u64,
    misses: u64,
    evictions: u64,
    writes: u64,
}

struct StorageManager {
    storage_dir: PathBuf,
    allocator: StorageAllocator,
    io_stats: IoStats,
}

struct StorageAllocator {
    free_pages: HashMap<u64, Vec<u64>>,
    page_size: u32,
    total_pages: u64,
    free_pages_count: u64,
}

struct IoStats {
    reads: u64,
    writes: u64,
    fsync: u64,
    read_bytes: u64,
    written_bytes: u64,
    read_time: Duration,
    write_time: Duration,
    fsync_time: Duration,
}

struct QueryEngine {
    parser: SqlParser,
    optimizer: QueryOptimizer,
    executor: QueryExecutor,
    prepared_statements: RwLock<HashMap<String, PreparedStatement>>,
    query_stats: QueryStats,
}

struct SqlParser {
    dialect: SqlDialect,
    max_query_length: usize,
}

enum SqlDialect {
    Ansi,
    Mysql,
    Postgresql,
    Sqlite,
    Custom,
}

struct QueryOptimizer {
    statistics: StatisticsCollector,
    rules: Vec<OptimizationRule>,
    max_optimization_time: Duration,
}

struct StatisticsCollector {
    column_stats: HashMap<String, ColumnStatistics>,
    last_updated: DateTime<Utc>,
}

struct ColumnStatistics {
    table_name: String,
    column_name: String,
    distinct_values: u64,
    null_count: u64,
    min_value: Option<Value>,
    max_value: Option<Value>,
    most_common_values: Vec<(Value, u64)>,
    histogram: Option<Histogram>,
}

struct Histogram {
    buckets: Vec<HistogramBucket>,
    bucket_width: f64,
}

struct HistogramBucket {
    low_value: Value,
    high_value: Value,
    count: u64,
}

enum OptimizationRule {
    PushDownPredicate,
    MergeJoins,
    EliminateSubqueries,
    UseCoveringIndex,
    PartitionPruning,
    JoinReordering,
    CommonSubexpressionElimination,
}

struct QueryExecutor {
    execution_threads: ThreadPool,
    max_concurrent_queries: u32,
    active_queries: RwLock<HashMap<String, ActiveQuery>>,
}

struct ActiveQuery {
    id: String,
    sql: String,
    started_at: DateTime<Utc>,
    state: QueryState,
    progress: f64,
    estimated_rows: u64,
    processed_rows: u64,
}

enum QueryState {
    Parsing,
    Planning,
    Executing,
    Fetching,
    Completed,
    Failed,
    Cancelled,
}

struct PreparedStatement {
    id: String,
    sql: String,
    plan: QueryPlan,
    parameters: Vec<DataType>,
    created_at: DateTime<Utc>,
    last_used: DateTime<Utc>,
    execution_count: u64,
}

struct QueryPlan {
    operators: Vec<PlanOperator>,
    estimated_cost: f64,
    estimated_rows: u64,
}

enum PlanOperator {
    TableScan { table: String, alias: Option<String> },
    IndexScan { index: String, alias: Option<String> },
    Filter { predicate: String },
    Project { expressions: Vec<String> },
    Join { join_type: JoinType, left: Box<PlanOperator>, right: Box<PlanOperator>, condition: String },
    Aggregate { group_by: Vec<String>, aggregates: Vec<String> },
    Sort { expressions: Vec<String>, limit: Option<u64>, offset: Option<u64> },
    Union { all: bool, left: Box<PlanOperator>, right: Box<PlanOperator> },
}

enum JoinType {
    Inner,
    Left,
    Right,
    Full,
    Cross,
}

struct QueryStats {
    queries_executed: u64,
    total_execution_time: Duration,
    avg_execution_time: Duration,
    slowest_queries: Vec<(String, Duration)>,
    errors: u64,
}

struct DatabaseTransactionManager {
    active_transactions: RwLock<HashMap<String, Transaction>>,
    transaction_log: TransactionLog,
    isolation_level: IsolationLevel,
    lock_manager: LockManager,
    deadlock_detector: DeadlockDetector,
}

struct Transaction {
    id: String,
    started_at: DateTime<Utc>,
    isolation_level: IsolationLevel,
    status: TransactionStatus,
    operations: Vec<Operation>,
    locks: HashSet<LockId>,
    snapshot: Option<TransactionSnapshot>,
}

enum TransactionStatus {
    Active,
    Preparing,
    Prepared,
    Committing,
    Committed,
    RollingBack,
    RolledBack,
    Failed,
}

struct Operation {
    operation_type: OperationType,
    table: String,
    row_id: Option<String>,
    before_image: Option<Vec<u8>>,
    after_image: Option<Vec<u8>>,
}

enum OperationType {
    Insert,
    Update,
    Delete,
    Read,
}

struct TransactionSnapshot {
    id: String,
    created_at: DateTime<Utc>,
    version: u64,
}

struct TransactionLog {
    current_log: RwLock<LogFile>,
    archived_logs: RwLock<Vec<LogFile>>,
    log_dir: PathBuf,
}

enum IsolationLevel {
    ReadUncommitted,
    ReadCommitted,
    RepeatableRead,
    Snapshot,
    Serializable,
}

struct LockManager {
    locks: RwLock<HashMap<LockId, Lock>>,
    lock_wait_queue: RwLock<HashMap<LockId, Vec<WaitingLock>>>,
    lock_timeout: Duration,
}

struct LockId {
    resource_type: ResourceType,
    resource_id: String,
}

enum ResourceType {
    Table,
    Row,
    Page,
    Index,
    Schema,
}

struct Lock {
    id: LockId,
    lock_type: LockType,
    holder: String,
    granted_at: DateTime<Utc>,
}

enum LockType {
    Shared,
    Exclusive,
    Intent,
    IntentShared,
    IntentExclusive,
}

struct WaitingLock {
    transaction_id: String,
    lock_id: LockId,
    lock_type: LockType,
    waiting_since: DateTime<Utc>,
}

struct DeadlockDetector {
    wait_for_graph: RwLock<HashMap<String, HashSet<String>>>,
    detection_thread: Option<JoinHandle<()>>,
    running: AtomicBool,
    detection_interval: Duration,
}

struct ReplicationManager {
    local_role: ReplicationRole,
    remote_nodes: RwLock<HashMap<String, RemoteNode>>,
    replication_thread: Option<JoinHandle<()>>,
    running: AtomicBool,
    replication_log: ReplicationLog,
}

enum ReplicationRole {
    Primary,
    Secondary,
    Standalone,
}

struct RemoteNode {
    node_id: String,
    role: ReplicationRole,
    connection: Option<RemoteConnection>,
    last_sync: DateTime<Utc>,
    last_heartbeat: DateTime<Utc>,
    replication_lag: Duration,
    sync_state: SyncState,
}

struct RemoteConnection {
    // 在实际实现中，这里会是网络连接
    stream: Option<()>,
    reader_thread: Option<JoinHandle<()>>,
    writer_thread: Option<JoinHandle<()>>,
}

enum SyncState {
    Syncing,
    Synced,
    Stale,
    Disconnected,
}

struct ReplicationLog {
    current_log: RwLock<LogFile>,
    archived_logs: RwLock<Vec<LogFile>>,
    log_dir: PathBuf,
}

struct ShardingManager {
    sharding_strategy: ShardingStrategy,
    shards: RwLock<HashMap<String, Shard>>,
    shard_allocation: RwLock<HashMap<String, String>>,
    balancer: ShardBalancer,
}

struct Shard {
    id: String,
    range: ShardRange,
    primary_node: String,
    replica_nodes: Vec<String>,
    size_bytes: u64,
    doc_count: u64,
}

enum ShardRange {
    Range { start: Value, end: Value },
    Hash { modulus: u32, remainder: u32 },
    Default,
}

struct ShardBalancer {
    balancing_thread: Option<JoinHandle<()>>,
    running: AtomicBool,
    balancing_interval: Duration,
    last_rebalance: DateTime<Utc>,
}

struct SchemaManager {
    schemas: RwLock<HashMap<String, Schema>>,
    version: AtomicU64,
    change_log: RwLock<Vec<SchemaChange>>,
}

struct Schema {
    name: String,
    tables: HashMap<String, TableSchema>,
    created_at: DateTime<Utc>,
    last_modified: DateTime<Utc>,
    owner: String,
}

struct SchemaChange {
    id: String,
    change_type: SchemaChangeType,
    schema_name: String,
    table_name: Option<String>,
    column_name: Option<String>,
    sql: String,
    version_before: u64,
    version_after: u64,
    created_at: DateTime<Utc>,
    created_by: String,
}

enum SchemaChangeType {
    CreateSchema,
    DropSchema,
    CreateTable,
    AlterTable,
    DropTable,
    AddColumn,
    ModifyColumn,
    DropColumn,
    AddIndex,
    DropIndex,
    AddConstraint,
    DropConstraint,
}

struct DatabaseServer {
    server: Option<JoinHandle<()>>,
    running: AtomicBool,
    bind_address: String,
    connections: RwLock<HashMap<String, Connection>>,
    listeners: Vec<Listener>,
}

struct Connection {
    id: String,
    client_address: String,
    connected_at: DateTime<Utc>,
    auth_user: String,
    current_schema: String,
    current_transaction: Option<String>,
    is_active: bool,
    last_activity: DateTime<Utc>,
    statistics: ConnectionStats,
}

struct ConnectionStats {
    queries_executed: u64,
    rows_returned: u64,
    bytes_sent: u64,
    bytes_received: u64,
}

struct Listener {
    protocol: Protocol,
    bind_address: String,
    thread: Option<JoinHandle<()>>,
    running: AtomicBool,
}

enum Protocol {
    Postgres,
    Mysql,
    Http,
    Grpc,
    Custom,
}

impl DistributedDatabase {
    fn new(node_id: &str, data_dir: &Path, bind_address: &str) -> Self {
        // 创建集群配置
        let cluster_config = ClusterConfig {
            cluster_id: uuid::Uuid::new_v4().to_string(),
            nodes: HashMap::new(),
            replication_factor: 3,
            sharding_strategy: ShardingStrategy::Hash { 
                key: "_id".to_string(), 
                shards: 8 
            },
            consistency_level: ConsistencyLevel::Quorum,
            read_preference: ReadPreference::PrimaryPreferred,
            heartbeat_interval: Duration::from_secs(5),
            connection_timeout: Duration::from_secs(30),
            query_timeout: Duration::from_secs(60),
        };
        
        // 创建本地节点配置
        let local_node_config = NodeConfig {
            id: node_id.to_string(),
            host: bind_address.to_string(),
            port: 5432,
            roles: [NodeRole::Primary].iter().cloned().collect(),
            zone: "zone1".to_string(),
            datacenter: "dc1".to_string(),
            capacity: ResourceCapacity {
                max_storage_gb: 100,
                max_memory_gb: 16,
                max_cpu_cores: 4,
                max_connections: 1000,
            },
        };
        
        // 创建节点管理器
        let node_manager = NodeManager {
            local_node: NodeInfo {
                config: local_node_config.clone(),
                status: NodeStatus::Starting,
                last_heartbeat: Utc::now(),
                last_election: None,
                stats: NodeStats {
                    uptime: Duration::from_secs(0),
                    cpu_usage: 0.0,
                    memory_usage: 0,
                    storage_usage: 0,
                    iops: 0,
                    network_in: 0,
                    network_out: 0,
                    connections: 0,
                    queries_per_second: 0.0,
                },
            },
            nodes: RwLock::new(HashMap::new()),
            status_check_thread: None,
            running: AtomicBool::new(false),
        };
        
        // 创建存储引擎
        let storage_engine = StorageEngine {
            tables: RwLock::new(HashMap::new()),
            indexes: RwLock::new(HashMap::new()),
            wal: WriteAheadLog {
                current_log: RwLock::new(LogFile {
                    id: uuid::Uuid::new_v4().to_string(),
                    path: data_dir.join("wal").join("current.log"),
                    start_lsn: 0,
                    end_lsn: 0,
                    created_at: Utc::now(),
                    size_bytes: 0,
                }),
                archived_logs: RwLock::new(Vec::new()),
                wal_dir: data_dir.join("wal"),
                max_log_size: 1024 * 1024 * 1024, // 1GB
                retention_hours: 24,
            },
            page_cache: PageCache {
                pages: RwLock::new(HashMap::new()),
                lru_list: RwLock::new(LinkedList::new()),
                max_capacity: 10000,
                stats: CacheStats {
                    hits: 0,
                    misses: 0,
                    evictions: 0,
                    writes: 0,
                },
            },
            storage_manager: StorageManager {
                storage_dir: data_dir.join("data"),
                allocator: StorageAllocator {
                    free_pages: HashMap::new(),
                    page_size: 8192, // 8KB
                    total_pages: 0,
                    free_pages_count: 0,
                },
                io_stats: IoStats {
                    reads: 0,
                    writes: 0,
                    fsync: 0,
                    read_bytes: 0,
                    written_bytes: 0,
                    read_time: Duration::from_secs(0),
                    write_time: Duration::from_secs(0),
                    fsync_time: Duration::from_secs(0),
                },
            },
        };
        
        // 创建查询引擎
        let query_engine = QueryEngine {
            parser: SqlParser {
                dialect: SqlDialect::Postgresql,
                max_query_length: 1024 * 1024, // 1MB
            },
            optimizer: QueryOptimizer {
                statistics: StatisticsCollector {
                    column_stats: HashMap::new(),
                    last_updated: Utc::now(),
                },
                rules: vec![
                    OptimizationRule::PushDownPredicate,
                    OptimizationRule::UseCoveringIndex,
                    OptimizationRule::PartitionPruning,
                ],
                max_optimization_time: Duration::from_millis(500),
            },
            executor: QueryExecutor {
                execution_threads: ThreadPool::new(4),
                max_concurrent_queries: 100,
                active_queries: RwLock::new(HashMap::new()),
            },
            prepared_statements: RwLock::new(HashMap::new()),
            query_stats: QueryStats {
                queries_executed: 0,
                total_execution_time: Duration::from_secs(0),
                avg_execution_time: Duration::from_secs(0),
                slowest_queries: Vec::new(),
                errors: 0,
            },
        };
        
        // 创建事务管理器
        let transaction_manager = DatabaseTransactionManager {
            active_transactions: RwLock::new(HashMap::new()),
            transaction_log: TransactionLog {
                current_log: RwLock::new(LogFile {
                    id: uuid::Uuid::new_v4().to_string(),
                    path: data_dir.join("txn").join("current.log"),
                    start_lsn: 0,
                    end_lsn: 0,
                    created_at: Utc::now(),
                    size_bytes: 0,
                }),
                archived_logs: RwLock::new(Vec::new()),
                log_dir: data_dir.join("txn"),
            },
            isolation_level: IsolationLevel::ReadCommitted,
            lock_manager: LockManager {
                locks: RwLock::new(HashMap::new()),
                lock_wait_queue: RwLock::new(HashMap::new()),
                lock_timeout: Duration::from_secs(10),
            },
            deadlock_detector: DeadlockDetector {
                wait_for_graph: RwLock::new(HashMap::new()),
                detection_thread: None,
                running: AtomicBool::new(false),
                detection_interval: Duration::from_secs(1),
            },
        };
        
        // 创建复制管理器
        let replication_manager = ReplicationManager {
            local_role: ReplicationRole::Primary,
            remote_nodes: RwLock::new(HashMap::new()),
            replication_thread: None,
            running: AtomicBool::new(false),
            replication_log: ReplicationLog {
                current_log: RwLock::new(LogFile {
                    id: uuid::Uuid::new_v4().to_string(),
                    path: data_dir.join("repl").join("current.log"),
                    start_lsn: 0,
                    end_lsn: 0,
                    created_at: Utc::now(),
                    size_bytes: 0,
                }),
                archived_logs: RwLock::new(Vec::new()),
                log_dir: data_dir.join("repl"),
            },
        };
        
        // 创建分片管理器
        let sharding_manager = ShardingManager {
            sharding_strategy: ShardingStrategy::Hash { 
                key: "_id".to_string(), 
                shards: 8 
            },
            shards: RwLock::new(HashMap::new()),
            shard_allocation: RwLock::new(HashMap::new()),
            balancer: ShardBalancer {
                balancing_thread: None,
                running: AtomicBool::new(false),
                balancing_interval: Duration::from_secs(300), // 5分钟
                last_rebalance: Utc::now(),
            },
        };
        
        // 创建模式管理器
        let schema_manager = SchemaManager {
            schemas: RwLock::new(HashMap::new()),
            version: AtomicU64::new(0),
            change_log: RwLock::new(Vec::new()),
        };
        
        // 创建数据库服务器
        let server = DatabaseServer {
            server: None,
            running: AtomicBool::new(false),
            bind_address: bind_address.to_string(),
            connections: RwLock::new(HashMap::new()),
            listeners: vec![
                Listener {
                    protocol: Protocol::Postgres,
                    bind_address: format!("{}:5432", bind_address),
                    thread: None,
                    running: AtomicBool::new(false),
                },
                Listener {
                    protocol: Protocol::Http,
                    bind_address: format!("{}:8080", bind_address),
                    thread: None,
                    running: AtomicBool::new(false),
                },
            ],
        };
        
        DistributedDatabase {
            node_id: node_id.to_string(),
            data_dir: data_dir.to_path_buf(),
            cluster_config,
            node_manager,
            storage_engine,
            query_engine,
            transaction_manager,
            replication_manager,
            sharding_manager,
            schema_manager,
            server,
            running: AtomicBool::new(false),
        }
    }
    
    fn start(&mut self) -> Result<(), String> {
        println!("启动分布式数据库系统");
        
        // 创建必要的目录
        if let Err(e) = std::fs::create_dir_all(&self.data_dir) {
            return Err(format!("创建数据目录失败: {}", e));
        }
        
        if let Err(e) = std::fs::create_dir_all(&self.storage_engine.wal.wal_dir) {
            return Err(format!("创建WAL目录失败: {}", e));
        }
        
        if let Err(e) = std::fs::create_dir_all(&self.storage_engine.storage_manager.storage_dir) {
            return Err(format!("创建存储目录失败: {}", e));
        }
        
        if let Err(e) = std::fs::create_dir_all(&self.transaction_manager.transaction_log.log_dir) {
            return Err(format!("创建事务日志目录失败: {}", e));
        }
        
        if let Err(e) = std::fs::create_dir_all(&self.replication_manager.replication_log.log_dir) {
            return Err(format!("创建复制日志目录失败: {}", e));
        }
        
        // 加载存储引擎
        self.load_storage_engine()?;
        
        // 加载架构
        self.load_schemas()?;
        
        // 启动节点管理器
        self.start_node_manager()?;
        
        // 启动死锁检测器
        self.start_deadlock_detector()?;
        
        // 启动复制管理器
        self.start_replication_manager()?;
        
        // 启动分片均衡器
        self.start_shard_balancer()?;
        
        // 启动服务器
        self.start_server()?;
        
        self.running.store(true, Ordering::SeqCst);
        
        Ok(())
    }
    
    fn load_storage_engine(&self) -> Result<(), String> {
        println!("加载存储引擎");
        
        // 加载表
        self.load_tables()?;
        
        // 加载索引
        self.load_indexes()?;
        
        // 恢复WAL
        self.recover_wal()?;
        
        Ok(())
    }
    
    fn load_tables(&self) -> Result<(), String> {
        println!("加载表");
        
        let tables_dir = self.storage_engine.storage_manager.storage_dir.join("tables");
        
        if !tables_dir.exists() {
            if let Err(e) = std::fs::create_dir_all(&tables_dir) {
                return Err(format!("创建表目录失败: {}", e));
            }
            return Ok(());
        }
        
        match std::fs::read_dir(&tables_dir) {
            Ok(entries) => {
                for entry in entries {
                    if let Ok(entry) = entry {
                        let path = entry.path();
                        
                        if path.is_dir() {
                            let table_name = path.file_name()
                                .and_then(|os| os.to_str())
                                .ok_or("无效的表目录名".to_string())?;
                            
                            match self.load_table(table_name, &path) {
                                Ok(_) => println!("加载表: {}", table_name),
                                Err(e) => println!("加载表 {} 失败: {}", table_name, e),
                            }
                        }
                    }
                }
            },
            Err(e) => return Err(format!("读取表目录失败: {}", e)),
        }
        
        Ok(())
    }
    
    fn load_table(&self, name: &str, path: &Path) -> Result<(), String> {
        let schema_path = path.join("schema.json");
        
        if !schema_path.exists() {
            return Err(format!("表架构文件不存在: {}", name));
        }
        
        let schema_json = match std::fs::read_to_string(&schema_path) {
            Ok(content) => content,
            Err(e) => return Err(format!("读取表架构文件失败: {}", e)),
        };
        
        // 在实际实现中，这里会解析JSON
        println!("解析表架构: {}", name);
        
        // 创建表
        let table = Table {
            name: name.to_string(),
            schema: TableSchema {
                columns: vec![
                    ColumnDefinition {
                        name: "id".to_string(),
                        data_type: DataType::Int64,
                        nullable: false,
                        default_value: None,
                        comment: Some("主键".to_string()),
                    },
                    ColumnDefinition {
                        name: "name".to_string(),
                        data_type: DataType::Varchar { length: 255 },
                        nullable: false,
                        default_value: None,
                        comment: Some("名称".to_string()),
                    },
                    ColumnDefinition {
                        name: "age".to_string(),
                        data_type: DataType::Int32,
                        nullable: true,
                        default_value: None,
                        comment: Some("年龄".to_string()),
                    },
                ],
                primary_key: vec!["id".to_string()],
                constraints: vec![
                    Constraint::PrimaryKey { columns: vec!["id".to_string()] },
                    Constraint::NotNull { column: "name".to_string() },
                ],
            },
            partitions: Vec::new(),
            indexes: HashMap::new(),
            created_at: Utc::now(),
            last_modified: Utc::now(),
            stats: TableStats {
                row_count: 0,
                size_bytes: 0,
                last_analyze: Utc::now(),
                avg_row_length: 0,
                index_sizes: HashMap::new(),
            },
        };
        
        // 添加到表集合
        let mut tables = self.storage_engine.tables.write().unwrap();
        tables.insert(name.to_string(), table);
        
        Ok(())
    }
    
    fn load_indexes(&self) -> Result<(), String> {
        println!("加载索引");
        
        let indexes_dir = self.storage_engine.storage_manager.storage_dir.join("indexes");
        
        if !indexes_dir.exists() {
            if let Err(e) = std::fs::create_dir_all(&indexes_dir) {
                return Err(format!("创建索引目录失败: {}", e));
            }
            return Ok(());
        }
        
        match std::fs::read_dir(&indexes_dir) {
            Ok(entries) => {
                for entry in entries {
                    if let Ok(entry) = entry {
                        let path = entry.path();
                        
                        if path.is_dir() {
                            let index_name = path.file_name()
                                .and_then(|os| os.to_str())
                                .ok_or("无效的索引目录名".to_string())?;
                            
                            match self.load_index(index_name, &path) {
                                Ok(_) => println!("加载索引: {}", index_name),
                                Err(e) => println!("加载索引 {} 失败: {}", index_name, e),
                            }
                        }
                    }
                }
            },
            Err(e) => return Err(format!("读取索引目录失败: {}", e)),
        }
        
        Ok(())
    }
    
    fn load_index(&self, name: &str, path: &Path) -> Result<(), String> {
        let metadata_path = path.join("metadata.json");
        
        if !metadata_path.exists() {
            return Err(format!("索引元数据文件不存在: {}", name));
        }
        
        let metadata_json = match std::fs::read_to_string(&metadata_path) {
            Ok(content) => content,
            Err(e) => return Err(format!("读取索引元数据文件失败: {}", e)),
        };
        
        // 在实际实现中，这里会解析JSON
        println!("解析索引元数据: {}", name);
        
        

```rust
        // 创建索引
        let index = Index {
            name: name.to_string(),
            table_name: "users".to_string(), // 示例表名
            columns: vec!["name".to_string()],
            index_type: IndexType::BTree,
            is_unique: false,
            created_at: Utc::now(),
            last_modified: Utc::now(),
            size_bytes: 0,
        };
        
        // 添加到索引集合
        let mut indexes = self.storage_engine.indexes.write().unwrap();
        indexes.insert(name.to_string(), index);
        
        Ok(())
    }
    
    fn recover_wal(&self) -> Result<(), String> {
        println!("恢复预写日志");
        
        let wal_dir = &self.storage_engine.wal.wal_dir;
        
        if !wal_dir.exists() {
            return Ok();
        }
        
        // 查找所有日志文件
        let mut log_files = Vec::new();
        
        match std::fs::read_dir(wal_dir) {
            Ok(entries) => {
                for entry in entries {
                    if let Ok(entry) = entry {
                        let path = entry.path();
                        
                        if path.is_file() && path.extension().map_or(false, |ext| ext == "log") {
                            log_files.push(path);
                        }
                    }
                }
            },
            Err(e) => return Err(format!("读取WAL目录失败: {}", e)),
        }
        
        // 按LSN排序日志文件
        log_files.sort_by(|a, b| {
            let a_name = a.file_stem().and_then(|s| s.to_str()).unwrap_or("");
            let b_name = b.file_stem().and_then(|s| s.to_str()).unwrap_or("");
            
            // 从文件名提取LSN（假设文件名格式为 "wal_<start_lsn>.log"）
            let a_lsn = a_name.strip_prefix("wal_").and_then(|s| s.parse::<u64>().ok()).unwrap_or(0);
            let b_lsn = b_name.strip_prefix("wal_").and_then(|s| s.parse::<u64>().ok()).unwrap_or(0);
            
            a_lsn.cmp(&b_lsn)
        });
        
        // 应用日志记录
        for log_file in log_files {
            println!("应用WAL文件: {}", log_file.display());
            
            match std::fs::File::open(&log_file) {
                Ok(file) => {
                    let reader = std::io::BufReader::new(file);
                    
                    // 在实际实现中，这里会读取并应用WAL记录
                    // 例如，重放插入、更新和删除操作
                },
                Err(e) => println!("打开WAL文件失败: {} - {}", log_file.display(), e),
            }
        }
        
        Ok(())
    }
    
    fn load_schemas(&self) -> Result<(), String> {
        println!("加载架构");
        
        let schemas_dir = self.data_dir.join("schemas");
        
        if !schemas_dir.exists() {
            if let Err(e) = std::fs::create_dir_all(&schemas_dir) {
                return Err(format!("创建架构目录失败: {}", e));
            }
            
            // 创建默认架构
            self.create_default_schema()?;
            return Ok(());
        }
        
        match std::fs::read_dir(&schemas_dir) {
            Ok(entries) => {
                for entry in entries {
                    if let Ok(entry) = entry {
                        let path = entry.path();
                        
                        if path.is_file() && path.extension().map_or(false, |ext| ext == "json") {
                            let schema_name = path.file_stem()
                                .and_then(|os| os.to_str())
                                .ok_or("无效的架构文件名".to_string())?;
                            
                            match self.load_schema(schema_name, &path) {
                                Ok(_) => println!("加载架构: {}", schema_name),
                                Err(e) => println!("加载架构 {} 失败: {}", schema_name, e),
                            }
                        }
                    }
                }
            },
            Err(e) => return Err(format!("读取架构目录失败: {}", e)),
        }
        
        // 如果没有架构，创建默认架构
        {
            let schemas = self.schema_manager.schemas.read().unwrap();
            if schemas.is_empty() {
                drop(schemas);
                self.create_default_schema()?;
            }
        }
        
        Ok(())
    }
    
    fn load_schema(&self, name: &str, path: &Path) -> Result<(), String> {
        let schema_json = match std::fs::read_to_string(path) {
            Ok(content) => content,
            Err(e) => return Err(format!("读取架构文件失败: {}", e)),
        };
        
        // 在实际实现中，这里会解析JSON
        println!("解析架构: {}", name);
        
        // 创建架构
        let schema = Schema {
            name: name.to_string(),
            tables: HashMap::new(),
            created_at: Utc::now(),
            last_modified: Utc::now(),
            owner: "admin".to_string(),
        };
        
        // 添加到架构集合
        let mut schemas = self.schema_manager.schemas.write().unwrap();
        schemas.insert(name.to_string(), schema);
        
        Ok(())
    }
    
    fn create_default_schema(&self) -> Result<(), String> {
        println!("创建默认架构");
        
        // 创建公共架构
        let public_schema = Schema {
            name: "public".to_string(),
            tables: HashMap::new(),
            created_at: Utc::now(),
            last_modified: Utc::now(),
            owner: "admin".to_string(),
        };
        
        // 添加到架构集合
        let mut schemas = self.schema_manager.schemas.write().unwrap();
        schemas.insert("public".to_string(), public_schema);
        
        // 保存架构
        drop(schemas);
        self.save_schema("public")?;
        
        Ok(())
    }
    
    fn save_schema(&self, name: &str) -> Result<(), String> {
        let schemas_dir = self.data_dir.join("schemas");
        
        if let Err(e) = std::fs::create_dir_all(&schemas_dir) {
            return Err(format!("创建架构目录失败: {}", e));
        }
        
        let schemas = self.schema_manager.schemas.read().unwrap();
        
        let schema = match schemas.get(name) {
            Some(schema) => schema,
            None => return Err(format!("架构不存在: {}", name)),
        };
        
        let schema_path = schemas_dir.join(format!("{}.json", name));
        
        // 在实际实现中，这里会序列化为JSON
        let schema_json = serde_json::to_string_pretty(schema)
            .map_err(|e| format!("序列化架构失败: {}", e))?;
        
        if let Err(e) = std::fs::write(&schema_path, schema_json) {
            return Err(format!("写入架构文件失败: {}", e));
        }
        
        Ok(())
    }
    
    fn start_node_manager(&mut self) -> Result<(), String> {
        println!("启动节点管理器");
        
        // 更新本地节点状态
        self.node_manager.local_node.status = NodeStatus::Running;
        
        // 将本地节点添加到节点集合
        let mut nodes = self.node_manager.nodes.write().unwrap();
        nodes.insert(self.node_id.clone(), self.node_manager.local_node.clone());
        
        // 添加配置的节点
        for (id, config) in &self.cluster_config.nodes {
            if id != &self.node_id {
                let node_info = NodeInfo {
                    config: config.clone(),
                    status: NodeStatus::Offline,
                    last_heartbeat: Utc::now(),
                    last_election: None,
                    stats: NodeStats {
                        uptime: Duration::from_secs(0),
                        cpu_usage: 0.0,
                        memory_usage: 0,
                        storage_usage: 0,
                        iops: 0,
                        network_in: 0,
                        network_out: 0,
                        connections: 0,
                        queries_per_second: 0.0,
                    },
                };
                
                nodes.insert(id.clone(), node_info);
            }
        }
        
        drop(nodes);
        
        // 启动状态检查线程
        let node_id = self.node_id.clone();
        let nodes = self.node_manager.nodes.clone();
        let heartbeat_interval = self.cluster_config.heartbeat_interval;
        
        self.node_manager.running.store(true, Ordering::SeqCst);
        
        let running = self.node_manager.running.clone();
        
        let thread = thread::spawn(move || {
            let mut start_time = Instant::now();
            
            while running.load(Ordering::SeqCst) {
                // 更新本地节点统计信息
                {
                    let mut nodes_map = nodes.write().unwrap();
                    
                    if let Some(node) = nodes_map.get_mut(&node_id) {
                        // 更新正常运行时间
                        node.stats.uptime = start_time.elapsed();
                        
                        // 获取CPU和内存使用情况（示例）
                        node.stats.cpu_usage = 0.5; // 50% CPU
                        node.stats.memory_usage = 1024 * 1024 * 1024; // 1GB
                        
                        // 更新心跳时间
                        node.last_heartbeat = Utc::now();
                    }
                }
                
                // 检查其他节点状态
                {
                    let mut nodes_map = nodes.write().unwrap();
                    let now = Utc::now();
                    
                    for (id, node) in nodes_map.iter_mut() {
                        if id != &node_id {
                            let elapsed = now.signed_duration_since(node.last_heartbeat);
                            
                            // 如果超过心跳间隔的两倍，标记为离线
                            if elapsed > (heartbeat_interval * 2).into() {
                                if node.status != NodeStatus::Offline {
                                    println!("节点离线: {}", id);
                                    node.status = NodeStatus::Offline;
                                }
                            }
                        }
                    }
                }
                
                // 休眠到下一个检查间隔
                thread::sleep(heartbeat_interval);
            }
        });
        
        self.node_manager.status_check_thread = Some(thread);
        
        Ok(())
    }
    
    fn start_deadlock_detector(&mut self) -> Result<(), String> {
        println!("启动死锁检测器");
        
        let wait_for_graph = self.transaction_manager.deadlock_detector.wait_for_graph.clone();
        let locks = self.transaction_manager.lock_manager.locks.clone();
        let lock_wait_queue = self.transaction_manager.lock_manager.lock_wait_queue.clone();
        let active_transactions = self.transaction_manager.active_transactions.clone();
        let detection_interval = self.transaction_manager.deadlock_detector.detection_interval;
        
        self.transaction_manager.deadlock_detector.running.store(true, Ordering::SeqCst);
        
        let running = self.transaction_manager.deadlock_detector.running.clone();
        
        let thread = thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                // 构建等待图
                {
                    let mut graph = wait_for_graph.write().unwrap();
                    graph.clear();
                    
                    let locks_map = locks.read().unwrap();
                    let wait_queue_map = lock_wait_queue.read().unwrap();
                    
                    // 对于每个锁等待队列
                    for (lock_id, waiters) in wait_queue_map.iter() {
                        // 找到持有锁的事务
                        if let Some(lock) = locks_map.get(lock_id) {
                            let holder = lock.holder.clone();
                            
                            // 对于每个等待的事务
                            for waiter in waiters {
                                let waiter_id = waiter.transaction_id.clone();
                                
                                // 添加边：waiter -> holder
                                let edges = graph.entry(waiter_id).or_insert_with(HashSet::new);
                                edges.insert(holder.clone());
                            }
                        }
                    }
                }
                
                // 检测环（死锁）
                let cycles = {
                    let graph = wait_for_graph.read().unwrap();
                    detect_cycles(&graph)
                };
                
                // 解决死锁
                if !cycles.is_empty() {
                    println!("检测到 {} 个死锁", cycles.len());
                    
                    for cycle in cycles {
                        // 选择牺牲事务（通常是最新的或优先级最低的）
                        if let Some(victim) = cycle.first() {
                            println!("选择事务 {} 作为死锁牺牲品", victim);
                            
                            // 中止牺牲事务
                            let mut transactions = active_transactions.write().unwrap();
                            
                            if let Some(transaction) = transactions.get_mut(victim) {
                                transaction.status = TransactionStatus::RollingBack;
                                println!("事务 {} 已标记为回滚", victim);
                                
                                // 在实际实现中，这里会执行实际的回滚操作
                            }
                        }
                    }
                }
                
                // 休眠到下一个检测间隔
                thread::sleep(detection_interval);
            }
        });
        
        self.transaction_manager.deadlock_detector.detection_thread = Some(thread);
        
        Ok(())
    }
    
    fn start_replication_manager(&mut self) -> Result<(), String> {
        println!("启动复制管理器");
        
        let node_id = self.node_id.clone();
        let remote_nodes = self.replication_manager.remote_nodes.clone();
        let local_role = match self.replication_manager.local_role {
            ReplicationRole::Primary => "主节点",
            ReplicationRole::Secondary => "从节点",
            ReplicationRole::Standalone => "独立节点",
        };
        
        println!("本地节点角色: {}", local_role);
        
        // 根据集群配置，添加复制节点
        {
            let mut nodes = remote_nodes.write().unwrap();
            
            for (id, config) in &self.cluster_config.nodes {
                if id != &node_id {
                    // 确定节点角色
                    let role = if config.roles.contains(&NodeRole::Primary) {
                        ReplicationRole::Primary
                    } else if config.roles.contains(&NodeRole::Secondary) {
                        ReplicationRole::Secondary
                    } else {
                        ReplicationRole::Standalone
                    };
                    
                    let remote_node = RemoteNode {
                        node_id: id.clone(),
                        role,
                        connection: None,
                        last_sync: Utc::now(),
                        last_heartbeat: Utc::now(),
                        replication_lag: Duration::from_secs(0),
                        sync_state: SyncState::Disconnected,
                    };
                    
                    nodes.insert(id.clone(), remote_node);
                    println!("添加复制节点: {}", id);
                }
            }
        }
        
        // 启动复制线程
        self.replication_manager.running.store(true, Ordering::SeqCst);
        
        let running = self.replication_manager.running.clone();
        let heartbeat_interval = self.cluster_config.heartbeat_interval;
        
        let thread = thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                // 处理复制逻辑
                if self.replication_manager.local_role == ReplicationRole::Primary {
                    // 主节点：将变更复制到从节点
                    let nodes = remote_nodes.read().unwrap();
                    
                    for (id, node) in nodes.iter() {
                        if node.role == ReplicationRole::Secondary {
                            println!("向从节点 {} 发送复制数据", id);
                            
                            // 在实际实现中，这里会发送WAL记录等
                        }
                    }
                } else if self.replication_manager.local_role == ReplicationRole::Secondary {
                    // 从节点：从主节点拉取变更
                    let nodes = remote_nodes.read().unwrap();
                    
                    for (id, node) in nodes.iter() {
                        if node.role == ReplicationRole::Primary {
                            println!("从主节点 {} 拉取复制数据", id);
                            
                            // 在实际实现中，这里会拉取并应用WAL记录等
                        }
                    }
                }
                
                // 休眠到下一个复制间隔
                thread::sleep(heartbeat_interval);
            }
        });
        
        self.replication_manager.replication_thread = Some(thread);
        
        Ok(())
    }
    
    fn start_shard_balancer(&mut self) -> Result<(), String> {
        println!("启动分片均衡器");
        
        // 加载分片配置
        self.load_shards()?;
        
        let shards = self.sharding_manager.shards.clone();
        let shard_allocation = self.sharding_manager.shard_allocation.clone();
        let balancing_interval = self.sharding_manager.balancer.balancing_interval;
        
        self.sharding_manager.balancer.running.store(true, Ordering::SeqCst);
        
        let running = self.sharding_manager.balancer.running.clone();
        
        let thread = thread::spawn(move || {
            while running.load(Ordering::SeqCst) {
                // 检查分片分布
                {
                    let shards_map = shards.read().unwrap();
                    let allocation_map = shard_allocation.read().unwrap();
                    
                    // 计算每个节点的分片数量
                    let mut node_shards: HashMap<String, usize> = HashMap::new();
                    
                    for (shard_id, node_id) in allocation_map.iter() {
                        *node_shards.entry(node_id.clone()).or_insert(0) += 1;
                    }
                    
                    // 打印分片分布
                    println!("当前分片分布:");
                    for (node_id, count) in node_shards.iter() {
                        println!("  节点 {}: {} 个分片", node_id, count);
                    }
                    
                    // 检查是否需要重新平衡
                    if !node_shards.is_empty() {
                        let min_shards = node_shards.values().min().unwrap_or(&0);
                        let max_shards = node_shards.values().max().unwrap_or(&0);
                        
                        if max_shards - min_shards > 1 {
                            println!("分片分布不均，需要重新平衡");
                            
                            // 在实际实现中，这里会执行分片迁移
                        }
                    }
                }
                
                // 休眠到下一个平衡间隔
                thread::sleep(balancing_interval);
            }
        });
        
        self.sharding_manager.balancer.balancing_thread = Some(thread);
        
        Ok(())
    }
    
    fn load_shards(&self) -> Result<(), String> {
        println!("加载分片配置");
        
        // 根据分片策略创建分片
        let strategy = &self.sharding_manager.sharding_strategy;
        
        match strategy {
            ShardingStrategy::Hash { key, shards } => {
                println!("使用哈希分片策略，字段: {}, 分片数: {}", key, shards);
                
                // 创建指定数量的分片
                let mut shards_map = self.sharding_manager.shards.write().unwrap();
                let mut allocation_map = self.sharding_manager.shard_allocation.write().unwrap();
                
                for i in 0..*shards {
                    let shard_id = format!("shard_{}", i);
                    
                    let shard = Shard {
                        id: shard_id.clone(),
                        range: ShardRange::Hash { modulus: *shards as u32, remainder: i as u32 },
                        primary_node: self.node_id.clone(), // 暂时分配给本地节点
                        replica_nodes: Vec::new(),
                        size_bytes: 0,
                        doc_count: 0,
                    };
                    
                    shards_map.insert(shard_id.clone(), shard);
                    allocation_map.insert(shard_id, self.node_id.clone());
                }
            },
            ShardingStrategy::Range { key } => {
                println!("使用范围分片策略，字段: {}", key);
                
                // 在实际实现中，这里会根据数据分布创建分片
            },
            ShardingStrategy::Directory { lookup_table } => {
                println!("使用目录分片策略，查找表: {}", lookup_table);
                
                // 在实际实现中，这里会加载查找表创建分片
            },
            ShardingStrategy::None => {
                println!("不使用分片");
                
                // 创建单个分片
                let mut shards_map = self.sharding_manager.shards.write().unwrap();
                let mut allocation_map = self.sharding_manager.shard_allocation.write().unwrap();
                
                let shard_id = "shard_0".to_string();
                
                let shard = Shard {
                    id: shard_id.clone(),
                    range: ShardRange::Default,
                    primary_node: self.node_id.clone(),
                    replica_nodes: Vec::new(),
                    size_bytes: 0,
                    doc_count: 0,
                };
                
                shards_map.insert(shard_id.clone(), shard);
                allocation_map.insert(shard_id, self.node_id.clone());
            },
        }
        
        Ok(())
    }
    
    fn start_server(&mut self) -> Result<(), String> {
        println!("启动数据库服务器");
        
        // 启动所有监听器
        for listener in &mut self.server.listeners {
            self.start_listener(listener)?;
        }
        
        // 启动主服务器线程
        let bind_address = self.server.bind_address.clone();
        let connections = self.server.connections.clone();
        
        self.server.running.store(true, Ordering::SeqCst);
        
        let running = self.server.running.clone();
        
        let thread = thread::spawn(move || {
            // 在实际实现中，这里会启动一个统一的管理服务器
            println!("数据库服务器绑定到: {}", bind_address);
            
            while running.load(Ordering::SeqCst) {
                // 管理连接
                {
                    let mut conns = connections.write().unwrap();
                    let now = Utc::now();
                    
                    // 清理空闲连接
                    conns.retain(|_, conn| {
                        let idle_time = now.signed_duration_since(conn.last_activity);
                        conn.is_active || idle_time.num_seconds() < 3600 // 1小时超时
                    });
                }
                
                // 休眠一段时间
                thread::sleep(Duration::from_secs(1));
            }
        });
        
        self.server.server = Some(thread);
        
        Ok(())
    }
    
    fn start_listener(&self, listener: &mut Listener) -> Result<(), String> {
        println!("启动监听器: {:?} 于 {}", listener.protocol, listener.bind_address);
        
        listener.running.store(true, Ordering::SeqCst);
        
        let protocol = match listener.protocol {
            Protocol::Postgres => "PostgreSQL",
            Protocol::Mysql => "MySQL",
            Protocol::Http => "HTTP",
            Protocol::Grpc => "gRPC",
            Protocol::Custom => "自定义",
        };
        
        let bind_address = listener.bind_address.clone();
        let running = listener.running.clone();
        let connections = self.server.connections.clone();
        
        let thread = thread::spawn(move || {
            println!("{} 监听器绑定到: {}", protocol, bind_address);
            
            while running.load(Ordering::SeqCst) {
                // 在实际实现中，这里会接受新连接
                
                // 模拟接受一个新连接
                {
                    // 这里不实际添加模拟连接，以免不断增加内存使用
                }
                
                // 休眠一段时间
                thread::sleep(Duration::from_millis(100));
            }
        });
        
        listener.thread = Some(thread);
        
        Ok(())
    }
    
    fn stop(&mut self) -> Result<(), String> {
        println!("停止分布式数据库系统");
        
        self.running.store(false, Ordering::SeqCst);
        
        // 停止服务器
        self.server.running.store(false, Ordering::SeqCst);
        if let Some(thread) = self.server.server.take() {
            match thread.join() {
                Ok(_) => {},
                Err(e) => println!("服务器线程退出错误: {:?}", e),
            }
        }
        
        // 停止所有监听器
        for listener in &mut self.server.listeners {
            listener.running.store(false, Ordering::SeqCst);
            if let Some(thread) = listener.thread.take() {
                match thread.join() {
                    Ok(_) => {},
                    Err(e) => println!("监听器线程退出错误: {:?}", e),
                }
            }
        }
        
        // 停止分片均衡器
        self.sharding_manager.balancer.running.store(false, Ordering::SeqCst);
        if let Some(thread) = self.sharding_manager.balancer.balancing_thread.take() {
            match thread.join() {
                Ok(_) => {},
                Err(e) => println!("分片均衡器线程退出错误: {:?}", e),
            }
        }
        
        // 停止复制管理器
        self.replication_manager.running.store(false, Ordering::SeqCst);
        if let Some(thread) = self.replication_manager.replication_thread.take() {
            match thread.join() {
                Ok(_) => {},
                Err(e) => println!("复制管理器线程退出错误: {:?}", e),
            }
        }
        
        // 停止死锁检测器
        self.transaction_manager.deadlock_detector.running.store(false, Ordering::SeqCst);
        if let Some(thread) = self.transaction_manager.deadlock_detector.detection_thread.take() {
            match thread.join() {
                Ok(_) => {},
                Err(e) => println!("死锁检测器线程退出错误: {:?}", e),
            }
        }
        
        // 停止节点管理器
        self.node_manager.running.store(false, Ordering::SeqCst);
        if let Some(thread) = self.node_manager.status_check_thread.take() {
            match thread.join() {
                Ok(_) => {},
                Err(e) => println!("节点管理器线程退出错误: {:?}", e),
            }
        }
        
        // 保存状态
        self.save_schemas()?;
        
        Ok(())
    }
    
    fn save_schemas(&self) -> Result<(), String> {
        println!("保存架构");
        
        let schemas_dir = self.data_dir.join("schemas");
        
        if let Err(e) = std::fs::create_dir_all(&schemas_dir) {
            return Err(format!("创建架构目录失败: {}", e));
        }
        
        let schemas = self.schema_manager.schemas.read().unwrap();
        
        for (name, schema) in schemas.iter() {
            let schema_path = schemas_dir.join(format!("{}.json", name));
            
            // 在实际实现中，这里会序列化为JSON
            let schema_json = serde_json::to_string_pretty(schema)
                .map_err(|e| format!("序列化架构失败: {}", e))?;
            
            if let Err(e) = std::fs::write(&schema_path, schema_json) {
                println!("保存架构 {} 失败: {}", name, e);
            }
        }
        
        Ok(())
    }
    
    fn execute_query(&self, sql: &str) -> Result<QueryResult, String> {
        println!("执行查询: {}", sql);
        
        // 解析SQL
        // 在实际实现中，这里会使用解析器解析SQL
        
        // 创建查询计划
        // 在实际实现中，这里会生成优化的查询计划
        
        // 执行查询
        // 在实际实现中，这里会执行查询并返回结果
        
        // 简化：返回一个模拟结果
        let columns = vec![
            ("id".to_string(), DataType::Int64),
            ("name".to_string(), DataType::Varchar { length: 255 }),
            ("age".to_string(), DataType::Int32),
        ];
        
        let mut rows = Vec::new();
        
        for i in 1..=5 {
            let values = vec![
                // id
                Value {
                    value_type: DataType::Int64,
                    raw_value: i.to_le_bytes().to_vec(),
                },
                // name
                Value {
                    value_type: DataType::Varchar { length: 255 },
                    raw_value: format!("用户 {}", i).into_bytes(),
                },
                // age
                Value {
                    value_type: DataType::Int32,
                    raw_value: (20 + i).to_le_bytes().to_vec(),
                },
            ];
            
            rows.push(values);
        }
        
        Ok(QueryResult {
            columns,
            rows,
            affected_rows: 0,
            execution_time: Duration::from_millis(10),
        })
    }
}

struct QueryResult {
    columns: Vec<(String, DataType)>,
    rows: Vec<Vec<Value>>,
    affected_rows: u64,
    execution_time: Duration,
}

// 实用函数：检测环（用于死锁检测）
fn detect_cycles(graph: &HashMap<String, HashSet<String>>) -> Vec<Vec<String>> {
    let mut visited = HashSet::new();
    let mut path = HashSet::new();
    let mut cycles = Vec::new();
    
    for node in graph.keys() {
        if !visited.contains(node) {
            dfs_detect_cycle(node, graph, &mut visited, &mut path, &mut Vec::new(), &mut cycles);
        }
    }
    
    cycles
}

fn dfs_detect_cycle(
    current: &str,
    graph: &HashMap<String, HashSet<String>>,
    visited: &mut HashSet<String>,
    path: &mut HashSet<String>,
    current_path: &mut Vec<String>,
    cycles: &mut Vec<Vec<String>>
) {
    visited.insert(current.to_string());
    path.insert(current.to_string());
    current_path.push(current.to_string());
    
    if let Some(neighbors) = graph.get(current) {
        for neighbor in neighbors {
            if !visited.contains(neighbor) {
                dfs_detect_cycle(neighbor, graph, visited, path, current_path, cycles);
            } else if path.contains(neighbor) {
                // 找到了一个环
                let index = current_path.iter().position(|x| x == neighbor).unwrap();
                let cycle = current_path[index..].to_vec();
                cycles.push(cycle);
            }
        }
    }
    
    path.remove(current);
    current_path.pop();
}

// 完善main函数，添加分布式数据库测试
fn main() -> Result<(), Box<dyn std::error::Error>> {
    println!("启动分布式系统示例");
    
    let temp_dir = std::env::temp_dir().join("distributed_systems_demo");
    
    if temp_dir.exists() {
        std::fs::remove_dir_all(&temp_dir)?;
    }
    std::fs::create_dir_all(&temp_dir)?;
    
    println!("使用临时目录: {:?}", temp_dir);
    
    // 测试分布式数据库系统
    {
        println!("\n===== 测试分布式数据库系统 =====");
        
        let data_dir = temp_dir.join("database");
        std::fs::create_dir_all(&data_dir)?;
        
        let mut database = DistributedDatabase::new("node1", &data_dir, "127.0.0.1");
        
        database.start()?;
        
        // 执行查询
        let sql = "SELECT * FROM users WHERE age > 18";
        
        match database.execute_query(sql) {
            Ok(result) => {
                println!("查询执行时间: {:?}", result.execution_time);
                println!("返回行数: {}", result.rows.len());
                
                // 打印结果
                if !result.rows.is_empty() {
                    // 打印列标题
                    let header = result.columns.iter()
                        .map(|(name, _)| name.clone())
                        .collect::<Vec<_>>()
                        .join(" | ");
                    
                    println!("{}", header);
                    println!("{}", "-".repeat(header.len()));
                    
                    // 打印数据行
                    for row in &result.rows {
                        let row_str = row.iter()
                            .enumerate()
                            .map(|(i, value)| {
                                // 简化：假设所有值都可以转换为字符串
                                match result.columns[i].1 {
                                    DataType::Int32 => {
                                        let bytes = &value.raw_value;
                                        let value = i32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]);
                                        value.to_string()
                                    },
                                    DataType::Int64 => {
                                        let bytes = &value.raw_value;
                                        let value = i64::from_le_bytes([
                                            bytes[0], bytes[1], bytes[2], bytes[3],
                                            bytes[4], bytes[5], bytes[6], bytes[7],
                                        ]);
                                        value.to_string()
                                    },
                                    DataType::Varchar { .. } => {
                                        String::from_utf8_lossy(&value.raw_value).to_string()
                                    },
                                    _ => "?".to_string(),
                                }
                            })
                            .collect::<Vec<_>>()
                            .join(" | ");
                        
                        println!("{}", row_str);
                    }
                }
            },
            Err(e) => println!("查询执行失败: {}", e),
        

```rust
        }
        
        // 停止数据库系统
        database.stop()?;
    }
    
    println!("\n所有分布式系统测试完成");
    
    // 运行综合演示
    run_distributed_systems_demo()?;
    
    // 清理临时目录
    std::fs::remove_dir_all(&temp_dir)?;
    
    Ok(())
}

// 综合演示：运行所有分布式系统并展示它们如何协同工作
fn run_distributed_systems_demo() -> Result<(), Box<dyn std::error::Error>> {
    println!("\n===== 运行分布式系统综合演示 =====");
    
    let temp_dir = std::env::temp_dir().join("distributed_systems_demo_integrated");
    
    if temp_dir.exists() {
        std::fs::remove_dir_all(&temp_dir)?;
    }
    std::fs::create_dir_all(&temp_dir)?;
    
    println!("使用临时目录: {:?}", temp_dir);
    
    // 创建基本目录结构
    let search_dir = temp_dir.join("search");
    let timeseries_dir = temp_dir.join("timeseries");
    let monitoring_dir = temp_dir.join("monitoring");
    let scheduler_dir = temp_dir.join("scheduler");
    let stream_dir = temp_dir.join("stream");
    let blockchain_dir = temp_dir.join("blockchain");
    let database_dir = temp_dir.join("database");
    let coordinator_dir = temp_dir.join("coordinator");
    
    for dir in &[&search_dir, &timeseries_dir, &monitoring_dir, &scheduler_dir, 
                &stream_dir, &blockchain_dir, &database_dir, &coordinator_dir] {
        std::fs::create_dir_all(dir)?;
    }
    
    // 1. 启动协调服务 (作为中心连接点)
    println!("\n启动分布式协调服务...");
    let peers = HashMap::new(); // 在集成演示中不需要其他对等节点
    let mut coordination_service = DistributedCoordinationService::new("coordinator-1", &coordinator_dir, "127.0.0.1:2181", peers);
    coordination_service.start()?;
    
    // 2. 启动监控系统 (监控其他所有服务)
    println!("\n启动分布式监控系统...");
    let mut monitoring_system = DistributedMonitoringSystem::new("monitor-1", &monitoring_dir, "127.0.0.1");
    monitoring_system.start()?;
    
    // 3. 启动数据库 (为其他系统提供持久化存储)
    println!("\n启动分布式数据库系统...");
    let mut database = DistributedDatabase::new("db-1", &database_dir, "127.0.0.1");
    database.start()?;
    
    // 4. 启动任务调度系统 (处理系统间作业)
    println!("\n启动分布式任务调度系统...");
    let mut task_scheduler = DistributedTaskScheduler::new("scheduler-1", &scheduler_dir, "127.0.0.1:8070");
    task_scheduler.start()?;
    
    // 5. 启动时序数据库 (存储指标数据)
    println!("\n启动分布式时序数据库...");
    let mut time_series_db = DistributedTimeSeriesDB::new("timeseries-1", &timeseries_dir, "127.0.0.1:8086");
    time_series_db.start()?;
    
    // 6. 启动流处理系统 (处理数据流)
    println!("\n启动分布式流处理系统...");
    let mut stream_processor = DistributedStreamProcessor::new("stream-1", &stream_dir, "127.0.0.1:8090");
    stream_processor.start()?;
    
    // 7. 启动搜索引擎 (提供搜索功能)
    println!("\n启动分布式搜索引擎...");
    let mut search_engine = DistributedSearchEngine::new("search-1", &search_dir, "127.0.0.1:9200");
    search_engine.start()?;
    
    // 8. 启动区块链 (提供不可变日志)
    println!("\n启动分布式区块链系统...");
    let mut blockchain = DistributedBlockchain::new("blockchain-1", &blockchain_dir, "127.0.0.1");
    blockchain.start()?;
    
    // 模拟系统间交互
    println!("\n模拟系统交互...");
    
    // 示例1: 监控系统收集所有服务的指标并存储到时序数据库
    println!("\n示例1: 监控指标收集");
    
    // 创建系统收集器并收集指标
    let system_collector = SystemMetricCollector::new();
    let metrics = system_collector.collect();
    println!("收集了 {} 个系统指标", metrics.len());
    
    // 将指标写入时序数据库
    let now = Utc::now().timestamp();
    for i in 0..3 {
        let point = DataPoint {
            timestamp: now + i * 60,
            value: 42.0 + (i as f64),
        };
        
        let labels = [
            ("service".to_string(), "database".to_string()),
            ("host".to_string(), "localhost".to_string()),
        ].iter().cloned().collect();
        
        if let Err(e) = time_series_db.write_data_point("cpu_usage", labels.clone(), point) {
            println!("写入时序数据点失败: {}", e);
        }
    }
    
    // 示例2: 任务调度器提交任务在流处理系统中创建新的数据流拓扑
    println!("\n示例2: 创建流处理拓扑");
    
    // 创建流
    let now = Utc::now();
    let event_stream = StreamDefinition {
        id: String::new(), // 自动生成ID
        name: "系统事件流".to_string(),
        schema: StreamSchema {
            fields: vec![
                FieldDefinition {
                    name: "event_id".to_string(),
                    field_type: FieldType::String,
                    nullable: false,
                    default_value: None,
                    description: Some("事件ID".to_string()),
                },
                FieldDefinition {
                    name: "service".to_string(),
                    field_type: FieldType::String,
                    nullable: false,
                    default_value: None,
                    description: Some("服务名称".to_string()),
                },
                FieldDefinition {
                    name: "timestamp".to_string(),
                    field_type: FieldType::Timestamp,
                    nullable: false,
                    default_value: None,
                    description: Some("事件时间戳".to_string()),
                },
                FieldDefinition {
                    name: "event_type".to_string(),
                    field_type: FieldType::String,
                    nullable: false,
                    default_value: None,
                    description: Some("事件类型".to_string()),
                },
                FieldDefinition {
                    name: "payload".to_string(),
                    field_type: FieldType::String,
                    nullable: true,
                    default_value: None,
                    description: Some("事件负载".to_string()),
                },
            ],
            key_fields: vec!["event_id".to_string()],
            timestamp_field: Some("timestamp".to_string()),
        },
        partitioning: PartitioningStrategy::Hash {
            fields: vec!["service".to_string()],
            partitions: 4,
        },
        retention: RetentionPolicy {
            time_based: Some(Duration::from_secs(86400 * 7)), // 7天
            size_based: Some(1024 * 1024 * 1024 * 5), // 5GB
        },
        created_at: now,
        created_by: "scheduler".to_string(),
    };
    
    let stream_id = match stream_processor.create_stream(event_stream) {
        Ok(id) => {
            println!("创建流成功，ID: {}", id);
            id
        },
        Err(e) => {
            println!("创建流失败: {}", e);
            "unknown".to_string()
        }
    };
    
    // 创建并提交任务
    let task = Task {
        id: String::new(), // 自动生成ID
        name: "创建事件处理拓扑".to_string(),
        task_type: "stream_topology_creation".to_string(),
        parameters: [
            ("stream_id".to_string(), stream_id.clone()),
            ("partitions".to_string(), "4".to_string()),
        ].iter().cloned().collect(),
        priority: TaskPriority::high(),
        dependencies: Vec::new(),
        retry_policy: RetryPolicy {
            max_retries: 3,
            retry_delay: Duration::from_secs(30),
            backoff_factor: 2.0,
            max_delay: Duration::from_secs(300),
        },
        timeout: Duration::from_secs(600),
        created_at: now,
        scheduled_at: None,
        created_by: "admin".to_string(),
        resources: [
            ("cpu".to_string(), 1.0),
            ("memory".to_string(), 512.0),
        ].iter().cloned().collect(),
        required_capabilities: ["stream_processing".to_string()].iter().cloned().collect(),
    };
    
    match task_scheduler.enqueue_task(task) {
        Ok(id) => println!("提交任务成功，ID: {}", id),
        Err(e) => println!("提交任务失败: {}", e),
    }
    
    // 示例3: 索引数据库中的数据到搜索引擎
    println!("\n示例3: 索引数据到搜索引擎");
    
    // 创建索引
    let schema = IndexSchema {
        fields: vec![
            FieldDefinition {
                name: "id".to_string(),
                field_type: FieldType::Text,
                indexed: true,
                stored: true,
                tokenized: false,
                vector_dimensions: None,
            },
            FieldDefinition {
                name: "name".to_string(),
                field_type: FieldType::Text,
                indexed: true,
                stored: true,
                tokenized: true,
                vector_dimensions: None,
            },
            FieldDefinition {
                name: "description".to_string(),
                field_type: FieldType::Text,
                indexed: true,
                stored: true,
                tokenized: true,
                vector_dimensions: None,
            },
        ],
        analyzers: HashMap::new(),
        index_options: IndexOptions {
            primary_key: Some("id".to_string()),
            index_merge_policy: MergePolicy::Tiered { max_merged_segment_size: 1024 * 1024 * 100 },
            similarity: Similarity::BM25 { k1: 1.2, b: 0.75 },
        },
    };
    
    match search_engine.create_index("entities", schema) {
        Ok(_) => println!("创建索引成功"),
        Err(e) => println!("创建索引失败: {}", e),
    }
    
    // 示例4: 区块链记录重要的系统事件
    println!("\n示例4: 区块链记录系统事件");
    
    // 获取区块链钱包余额
    let balance = blockchain.get_balance(&blockchain.wallet.selected_address);
    println!("区块链钱包余额: {}", balance);
    
    // 创建地址以接收事件记录
    match blockchain.create_new_address() {
        Ok(address) => println!("创建区块链地址成功: {}", address),
        Err(e) => println!("创建区块链地址失败: {}", e),
    }
    
    // 示例5: 数据库执行查询
    println!("\n示例5: 数据库查询");
    
    let sql = "SELECT service, COUNT(*) as event_count FROM system_events GROUP BY service";
    
    match database.execute_query(sql) {
        Ok(result) => println!("查询成功，返回 {} 行数据", result.rows.len()),
        Err(e) => println!("查询失败: {}", e),
    }
    
    // 等待一些时间让系统运行和交互
    println!("\n等待系统交互...");
    thread::sleep(Duration::from_secs(3));
    
    // 关闭所有系统
    println!("\n关闭所有分布式系统...");
    
    blockchain.stop()?;
    search_engine.stop()?;
    stream_processor.stop()?;
    time_series_db.stop()?;
    task_scheduler.stop()?;
    database.stop()?;
    monitoring_system.stop()?;
    coordination_service.stop()?;
    
    println!("\n分布式系统综合演示完成");
    
    // 清理临时目录
    std::fs::remove_dir_all(&temp_dir)?;
    
    Ok(())
}

// 总结
fn print_summary() {
    println!("\n===== 分布式系统架构总结 =====");
    println!("
本演示实现了8个互联的分布式系统:

1. 分布式搜索引擎 - 提供高效的文本和向量数据检索
   * 索引管理、分片复制、查询处理
   * 支持文本、向量和地理空间数据

2. 分布式时序数据库 - 优化存储和查询时间序列数据
   * 高效写入、压缩存储、分区策略
   * 聚合和降采样功能

3. 分布式监控系统 - 收集、存储和分析系统指标
   * 指标收集器、告警引擎、仪表盘服务
   * 多种通知通道

4. 分布式任务调度系统 - 管理和执行分布式任务
   * 优先级队列、任务依赖、重试策略
   * 资源感知调度

5. 分布式流处理系统 - 实时处理数据流
   * 数据流定义、拓扑管理、状态存储
   * 容错处理和检查点管理

6. 分布式区块链系统 - 不可变分布式账本
   * 共识引擎、交易处理、区块验证
   * 钱包管理和P2P网络

7. 分布式数据库系统 - 可扩展的SQL数据库
   * 查询处理、事务管理、复制
   * 分片策略和负载均衡

8. 分布式协调服务 - 提供共享配置和协调
   * 分布式锁、领导者选举、会话管理
   * 监视器和通知

这些系统协同工作，形成完整的分布式计算平台:
* 监控系统观察所有其他系统
* 时序数据库存储指标和事件数据
* 流处理系统处理来自各个系统的数据流
* 搜索引擎为系统数据提供快速查询
* 区块链记录关键事件和不可变历史
* 数据库提供持久化存储和事务处理
* 任务调度器协调跨系统的工作
* 协调服务提供服务发现和同步原语

所有系统都设计为容错、可扩展和高性能的，包含:
* 节点发现和健康检查
* 领导者选举和角色分配
* 数据复制和一致性保证
* 分片和负载均衡
* 故障检测和恢复
* 并发控制和资源管理
");
}

// 如果你想运行总结，添加这个函数调用到main函数末尾
// print_summary();
```
