// The Hasher's loop in safe Rust, over its kernels and the stack
// (stack_core.rs): the library includes this file in src/lib.rs, and
// tools/verify/tree/rust/hashercore includes it too, for Aeneas. It uses
// Cv and CHUNK_LEN from its includer.

/// A chunk's state: its number and the bytes it has so far (at most
/// CHUNK_LEN).
pub trait Chunk {
    fn counter(&self) -> u64;
    fn len(&self) -> usize;
    /// The next bytes, at most CHUNK_LEN - len() of them.
    fn update(&mut self, input: &[u8]);
    /// An empty chunk's number, advanced by `chunks`.
    fn advance(&mut self, chunks: u64);
}

/// The kernels the Hasher's loop calls, beyond the stack's `Parent`.
pub trait Feed<C: Chunk>: Parent {
    /// The number of 1-bits of `x`.
    fn ones(&self, x: u64) -> usize;
    /// A whole subtree's length to hash next, from chunk `counter` with
    /// `remaining` (more than CHUNK_LEN) bytes to go: CHUNK_LEN times a
    /// power of two dividing `counter`, at most `remaining`.
    fn subtree_len(&self, counter: u64, remaining: usize) -> usize;
    /// An empty chunk, numbered `counter`.
    fn new_chunk(&self, counter: u64) -> C;
    /// A full chunk's chaining value.
    fn chunk_cv(&self, chunk: &C) -> Cv;
    /// The chaining value of `chunk` (CHUNK_LEN bytes), numbered `counter`.
    fn whole_chunk_cv(&self, chunk: &[u8], counter: u64) -> Cv;
    /// The chaining value of the subtree over `input` (more than one chunk),
    /// its first chunk numbered `counter`, computed another way where the
    /// kernels have one (None: they have none for it). `ahead` bytes follow.
    fn subtree_cv(&self, input: &[u8], ahead: usize, counter: u64) -> Option<Cv>;
    /// The chaining values of the two children of the subtree over `input`
    /// (more than one chunk), its first chunk numbered `counter`.
    fn children(&self, input: &[u8], ahead: usize, counter: u64) -> [Cv; 2];
}

/// The nodes a Hasher's output is computed from.
pub trait Nodes<C: Chunk, N> {
    /// The node of `chunk`, the last.
    fn chunk_node(&self, chunk: &C) -> N;
    /// The parent node of two chaining values.
    fn parent_node(&self, left: &Cv, right: &Cv) -> N;
    /// A node's chaining value.
    fn node_cv(&self, node: &N) -> Cv;
}

/// `cv`, the subtree from chunk `counter`, onto the stack: the stack's
/// values merged to the subtrees before it first (lazily: the top value
/// may still merge with the next).
pub fn push<C: Chunk, K: Feed<C>>(k: &K, stack: &mut CvStack, initial: u64, cv: Cv, counter: u64) {
    stack.merge(k, k.ones(counter - initial));
    stack.push(cv);
}

/// The partial chunk filled from `input`; when more input follows, the full
/// chunk goes onto the stack and a new chunk begins. Returns the rest.
pub fn fill<'a, C: Chunk, K: Feed<C>>(k: &K, chunk: &mut C, stack: &mut CvStack, initial: u64, input: &'a [u8]) -> &'a [u8] {
    if chunk.len() == 0 {
        return input;
    }
    let take = if CHUNK_LEN - chunk.len() < input.len() { CHUNK_LEN - chunk.len() } else { input.len() };
    chunk.update(&input[..take]);
    let rest = &input[take..];
    if rest.is_empty() {
        return rest;
    }
    let counter = chunk.counter();
    push(k, stack, initial, k.chunk_cv(chunk), counter);
    *chunk = k.new_chunk(counter + 1);
    rest
}

/// `input` after an empty chunk: whole subtrees onto the stack, then at most
/// a chunk into the chunk, and the stack merged behind it.
pub fn feed<C: Chunk, K: Feed<C>>(k: &K, chunk: &mut C, stack: &mut CvStack, initial: u64, input: &[u8]) {
    let mut input = input;
    while input.len() > CHUNK_LEN {
        let counter = chunk.counter();
        let len = k.subtree_len(counter, input.len());
        let chunks = (len / CHUNK_LEN) as u64;
        let ahead = input.len() - len;
        let sub = &input[..len];
        let flat = if counter > initial { k.subtree_cv(sub, ahead, counter) } else { None };
        match flat {
            Some(cv) => push(k, stack, initial, cv, counter),
            None => {
                if len <= CHUNK_LEN {
                    push(k, stack, initial, k.whole_chunk_cv(sub, counter), counter);
                } else {
                    let [left, right] = k.children(sub, ahead, counter);
                    push(k, stack, initial, left, counter);
                    push(k, stack, initial, right, counter + chunks / 2);
                }
            }
        }
        chunk.advance(chunks);
        input = &input[len..];
    }
    if !input.is_empty() {
        chunk.update(input);
        stack.merge(k, k.ones(chunk.counter() - initial));
    }
}

/// The root's node: the last chunk's (or the top two values' parent),
/// folded into the stack's values from the top.
pub fn final_node<C: Chunk, N, K: Nodes<C, N>>(k: &K, chunk: &C, stack: &CvStack) -> N {
    if stack.len() == 0 {
        return k.chunk_node(chunk);
    }
    let mut n = stack.len();
    let mut out = if chunk.len() > 0 {
        k.chunk_node(chunk)
    } else {
        n -= 2;
        k.parent_node(&stack.get(n), &stack.get(n + 1))
    };
    while n > 0 {
        n -= 1;
        out = k.parent_node(&stack.get(n), &k.node_cv(&out));
    }
    out
}

/// What the Hasher's kernels take from the library beyond the compression
/// function: Feed's methods of those names, as Feed describes them.
pub trait Hooks {
    fn ones(&self, x: u64) -> usize;
    fn subtree_len(&self, counter: u64, remaining: usize) -> usize;
    fn subtree_cv(&self, input: &[u8], ahead: usize, counter: u64) -> Option<Cv>;
    fn children(&self, input: &[u8], ahead: usize, counter: u64) -> [Cv; 2];
}

/// The Hasher's kernels: chunks, nodes, and parents on `key`, `flags`, and
/// `platform`, and the rest from `hooks`.
pub struct Kernels<'a, P, H> {
    pub key: &'a [u32; 8],
    pub flags: u8,
    pub platform: P,
    pub hooks: H,
}

impl<P: Blocks + Copy, H> Parent for Kernels<'_, P, H> {
    #[inline(always)]
    fn parent(&self, left: &Cv, right: &Cv) -> Cv {
        parent_output(left, right, self.key, self.flags, self.platform).chaining_value()
    }
}

impl<P: Blocks + Copy, H: Hooks> Feed<ChunkState<P>> for Kernels<'_, P, H> {
    #[inline(always)]
    fn ones(&self, x: u64) -> usize {
        self.hooks.ones(x)
    }

    #[inline(always)]
    fn subtree_len(&self, counter: u64, remaining: usize) -> usize {
        self.hooks.subtree_len(counter, remaining)
    }

    #[inline(always)]
    fn new_chunk(&self, counter: u64) -> ChunkState<P> {
        ChunkState::new(self.key, counter, self.flags, self.platform)
    }

    #[inline(always)]
    fn chunk_cv(&self, chunk: &ChunkState<P>) -> Cv {
        chunk.output().chaining_value()
    }

    #[inline(always)]
    fn whole_chunk_cv(&self, chunk: &[u8], counter: u64) -> Cv {
        let mut state = ChunkState::new(self.key, counter, self.flags, self.platform);
        state.absorb(chunk);
        state.output().chaining_value()
    }

    #[inline(always)]
    fn subtree_cv(&self, input: &[u8], ahead: usize, counter: u64) -> Option<Cv> {
        self.hooks.subtree_cv(input, ahead, counter)
    }

    #[inline(always)]
    fn children(&self, input: &[u8], ahead: usize, counter: u64) -> [Cv; 2] {
        self.hooks.children(input, ahead, counter)
    }
}

impl<P: Blocks + Copy, H> Nodes<ChunkState<P>, Output<P>> for Kernels<'_, P, H> {
    #[inline(always)]
    fn chunk_node(&self, chunk: &ChunkState<P>) -> Output<P> {
        chunk.output()
    }

    #[inline(always)]
    fn parent_node(&self, left: &Cv, right: &Cv) -> Output<P> {
        parent_output(left, right, self.key, self.flags, self.platform)
    }

    #[inline(always)]
    fn node_cv(&self, node: &Output<P>) -> Cv {
        node.chaining_value()
    }
}
