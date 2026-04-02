//! # The Cryptographic Layer of Biometric Authentication
//!
//! Implementation of the PiH and PiHC schemes.
//!
//! ## Acknowledgements
//! This implementation was developed with the assistance of Claude
//! (claude.ai), an AI assistant made by Anthropic. All cryptographic
//! logic and correctness were verified by the authors.

use ark_bn254::{Bn254, Fq12, Fr, G1Projective, G2Projective};
use ark_ec::pairing::Pairing;
use ark_ec::Group;
type GT = ark_ec::pairing::PairingOutput<Bn254>;
use ark_ff::{Field, PrimeField, UniformRand};
use ark_serialize::CanonicalSerialize;
use ark_std::{One, Zero};
use hashbrown::HashMap;
use rayon::prelude::*;

use std::time::Instant;

// ── Hamming Distance ──────────────────────────────────────────────────────────

pub fn hamming_distance(a: &[u8], b: &[u8]) -> usize {
    a.iter().zip(b.iter()).filter(|(x, y)| x != y).count()
}

// ── Matrix helpers ────────────────────────────────────────────────────────────

fn identity(n: usize) -> Vec<Vec<Fr>> {
    let mut m = vec![vec![Fr::zero(); n]; n];
    for i in 0..n {
        m[i][i] = Fr::one();
    }
    m
}

fn mat_inv(mat: &Vec<Vec<Fr>>) -> Option<Vec<Vec<Fr>>> {
    let n = mat.len();
    let mut aug: Vec<Vec<Fr>> = mat
        .iter()
        .enumerate()
        .map(|(i, row)| {
            let mut r = row.clone();
            r.extend(identity(n)[i].iter().copied());
            r
        })
        .collect();

    for col in 0..n {
        let pivot = (col..n).find(|&row| !aug[row][col].is_zero())?;
        aug.swap(col, pivot);
        let inv_pivot = aug[col][col].inverse()?;
        for j in 0..2 * n {
            aug[col][j] *= inv_pivot;
        }
        for row in 0..n {
            if row != col {
                let factor = aug[row][col];
                for j in 0..2 * n {
                    let sub = factor * aug[col][j];
                    aug[row][j] -= sub;
                }
            }
        }
    }
    Some((0..n).map(|i| aug[i][n..].to_vec()).collect())
}

fn transpose(m: &Vec<Vec<Fr>>) -> Vec<Vec<Fr>> {
    let n = m.len();
    (0..n)
        .map(|i| (0..n).map(|j| m[j][i]).collect())
        .collect()
}

// ── fhIPFE ────────────────────────────────────────────────────────────────────

pub struct MasterSecretKey {
    pub g1: G1Projective,
    pub g2: G2Projective,
    pub b: Vec<Vec<Fr>>,
    pub b_star: Vec<Vec<Fr>>,
}

pub struct SecretKey {
    pub k1: G2Projective,
    pub k2: Vec<G2Projective>,
}

pub struct Ciphertext {
    pub c1: G1Projective,
    pub c2: Vec<G1Projective>,
}

pub struct FhIPFE {
    pub size: usize,
}

impl FhIPFE {
    pub fn new(size: usize) -> Self {
        Self { size }
    }

    pub fn setup(&self) -> MasterSecretKey {
        let mut rng = ark_std::test_rng();
        let g1 = G1Projective::generator();
        let g2 = G2Projective::generator();
        let (b, b_star) = loop {
            let b: Vec<Vec<Fr>> = (0..self.size)
                .map(|_| (0..self.size).map(|_| Fr::rand(&mut rng)).collect())
                .collect();
            if let Some(b_inv) = mat_inv(&b) {
                break (b, transpose(&b_inv));
            }
        };
        MasterSecretKey { g1, g2, b, b_star }
    }

    pub fn k_gen(&self, msk: &MasterSecretKey, x: &[Fr]) -> Option<SecretKey> {
        if x.len() != self.size {
            eprintln!("[Error] x length {} ≠ size {}", x.len(), self.size);
            return None;
        }
        let mut rng = ark_std::test_rng();
        let alpha = Fr::rand(&mut rng);
        let k1 = msk.g2 * alpha;
        let k2: Vec<G2Projective> = (0..self.size)
            .into_par_iter()
            .map(|j| {
                let exp: Fr = x.iter().enumerate().map(|(i, xi)| *xi * msk.b[i][j]).sum();
                msk.g2 * (alpha * exp)
            })
            .collect();
        Some(SecretKey { k1, k2 })
    }

    pub fn enc(&self, msk: &MasterSecretKey, y: &[Fr]) -> Option<Ciphertext> {
        if y.len() != self.size {
            eprintln!("[Error] y length {} ≠ size {}", y.len(), self.size);
            return None;
        }
        let mut rng = ark_std::test_rng();
        let beta = Fr::rand(&mut rng);
        let c1 = msk.g1 * beta;
        let c2: Vec<G1Projective> = (0..self.size)
            .into_par_iter()
            .map(|j| {
                let exp: Fr = y.iter().enumerate().map(|(i, yi)| *yi * msk.b_star[i][j]).sum();
                msk.g1 * (beta * exp)
            })
            .collect();
        Some(Ciphertext { c1, c2 })
    }

    pub fn dec(&self, sk: &SecretKey, ct: &Ciphertext, tau: i64) -> Option<i64> {
        let d1 = Bn254::pairing(ct.c1, sk.k1);
        let d2 = Bn254::multi_pairing(ct.c2.clone(), sk.k2.clone());
        bsgs(d1, d2, tau)
    }
}

// ── Byte size reporting ───────────────────────────────────────────────────────

pub trait ByteSize {
    fn byte_size(&self) -> usize;
}

impl<T: CanonicalSerialize> ByteSize for T {
    fn byte_size(&self) -> usize {
        let mut buf = Vec::new();
        self.serialize_compressed(&mut buf).unwrap();
        buf.len()
    }
}

// SecretKey (em): K1 (G2) + K2 (vec of G2)
impl ByteSize for SecretKey {
    fn byte_size(&self) -> usize {
        self.k1.byte_size()
            + self.k2.iter().map(|k| k.byte_size()).sum::<usize>()
    }
}

// Ciphertext (pm): C1 (G1) + C2 (vec of G1)
impl ByteSize for Ciphertext {
    fn byte_size(&self) -> usize {
        self.c1.byte_size()
            + self.c2.iter().map(|c| c.byte_size()).sum::<usize>()
    }
}

// MasterSecretKey: g1 (G1) + g2 (G2) + B (n×n Fr) + B* (n×n Fr)
impl ByteSize for MasterSecretKey {
    fn byte_size(&self) -> usize {
        let n = self.b.len();
        self.g1.byte_size()
            + self.g2.byte_size()
            + 2 * n * n * Fr::zero().byte_size() // B and B* are n×n Fr matrices
    }
}

// ── Baby-step Giant-step ──────────────────────────────────────────────────────

fn serialize_fq12(gt: &Fq12) -> Vec<u8> {
    let mut buf = Vec::new();
    gt.serialize_compressed(&mut buf).unwrap();
    buf
}

pub fn bsgs(base: GT, target: GT, tau: i64) -> Option<i64> {
    let base = base.0;
    let target = target.0;
    let lb = -tau;
    let m = ((2 * tau + 1) as f64).sqrt().ceil() as i64;

    let base_lb = base.pow(Fr::from(lb.unsigned_abs()).into_bigint());
    let shifted_target = if lb < 0 {
        target * base_lb
    } else {
        target * base_lb.inverse().unwrap()
    };

    let mut baby_steps: HashMap<Vec<u8>, i64> = HashMap::new();
    let mut curr = Fq12::one();
    for j in 0..m {
        baby_steps.insert(serialize_fq12(&curr), j);
        curr *= base;
    }

    let base_inv_m = base.pow(Fr::from(m as u64).into_bigint()).inverse().unwrap();

    let mut giant = shifted_target;
    for i in 0..m {
        if let Some(&j) = baby_steps.get(&serialize_fq12(&giant)) {
            return Some(i * m + j + lb);
        }
        giant *= base_inv_m;
    }
    None
}

// ── PiH ───────────────────────────────────────────────────────────────────────
//
// Enroll key:  sk  for x = 2b - 1
// Probe ct:    ct  for y = 2b' - 1
// Comp:        HD(b, b') = (n - <x,y>) / 2

pub struct PiH {
    pub size: usize,
    fe: FhIPFE,
    msk: Option<MasterSecretKey>,
}

impl PiH {
    pub fn new(size: usize) -> Self {
        Self {
            size,
            fe: FhIPFE::new(size),
            msk: None,
        }
    }

    pub fn setup(&mut self) -> &MasterSecretKey {
        self.msk = Some(self.fe.setup());
        self.msk.as_ref().unwrap()
    }

    /// Enroll: binary vector b → enrollment message (SecretKey for x = 2b-1)
    pub fn enroll(&self, b: &[u8]) -> Option<SecretKey> {
        if !b.iter().all(|&bi| bi == 0 || bi == 1) {
            eprintln!("[Error] Input vector must be binary");
            return None;
        }
        let x: Vec<Fr> = b.iter().map(|&bi| if bi == 1 { Fr::one() } else { Fr::zero() - Fr::one() }).collect();
        self.fe.k_gen(self.msk.as_ref()?, &x)
    }

    /// Probe: binary vector b' → probe message (Ciphertext for y = 2b'-1)
    pub fn probe(&self, b: &[u8]) -> Option<Ciphertext> {
        if !b.iter().all(|&bi| bi == 0 || bi == 1) {
            eprintln!("[Error] Input vector must be binary");
            return None;
        }
        let y: Vec<Fr> = b.iter().map(|&bi| if bi == 1 { Fr::one() } else { Fr::zero() - Fr::one() }).collect();
        self.fe.enc(self.msk.as_ref()?, &y)
    }

    /// Comp: recover Hamming distance from (sk, ct)
    /// HD = (n - <x,y>) / 2
    pub fn comp(&self, sk: &SecretKey, ct: &Ciphertext) -> Option<i64> {
        let tau = self.size as i64 + 1;
        let s = self.fe.dec(sk, ct, tau)?;
        Some((self.size as i64 - s) / 2)
    }
}

// ── PiHC ──────────────────────────────────────────────────────────────────────
//
// Like PiH but with n consistency-check keys in csk.
// Each check key ski corresponds to ei * c[i] (unit vector scaled by ±1).
// Comp first verifies each ski gives Dec ∈ {-1, 1}, then computes HD.

pub struct PiHC {
    pub size: usize,
    fe: FhIPFE,
    msk: Option<MasterSecretKey>,
    check_keys: Vec<SecretKey>, // one per dimension
}

impl PiHC {
    pub fn new(size: usize) -> Self {
        Self {
            size,
            fe: FhIPFE::new(size),
            msk: None,
            check_keys: Vec::new(),
        }
    }

    pub fn setup(&mut self) {
        let mut rng = ark_std::test_rng();
        let msk = self.fe.setup();

        // c[i] ∈ {-1, +1} randomly; ski = KGen(msk, ei * c[i])
        self.check_keys = (0..self.size)
            .map(|i| {
                let ci: Fr = if rand_bit(&mut rng) {
                    Fr::one()
                } else {
                    Fr::zero() - Fr::one()
                };
                let mut e = vec![Fr::zero(); self.size];
                e[i] = ci;
                self.fe.k_gen(&msk, &e).expect("KGen failed in setup")
            })
            .collect();

        self.msk = Some(msk);
    }

    pub fn enroll(&self, b: &[u8]) -> Option<SecretKey> {
        if !b.iter().all(|&bi| bi == 0 || bi == 1) {
            eprintln!("[Error] Input vector must be binary");
            return None;
        }
        let x: Vec<Fr> = b.iter().map(|&bi| if bi == 1 { Fr::one() } else { Fr::zero() - Fr::one() }).collect();
        self.fe.k_gen(self.msk.as_ref()?, &x)
    }

    pub fn probe(&self, b: &[u8]) -> Option<Ciphertext> {
        if !b.iter().all(|&bi| bi == 0 || bi == 1) {
            eprintln!("[Error] Input vector must be binary");
            return None;
        }
        let y: Vec<Fr> = b.iter().map(|&bi| if bi == 1 { Fr::one() } else { Fr::zero() - Fr::one() }).collect();
        self.fe.enc(self.msk.as_ref()?, &y)
    }

    /// Comp: verify all check keys give ±1, then compute HD
    pub fn comp(&self, sk: &SecretKey, ct: &Ciphertext) -> Option<i64> {
        // Verification step
        for (i, ski) in self.check_keys.iter().enumerate() {
            match self.fe.dec(ski, ct, 1) {
                Some(s) if s == -1 || s == 1 => {}
                _ => {
                    eprintln!("[Verification Fault] check key {} failed", i);
                    return None;
                }
            }
        }
        // Compute HD
        let tau = self.size as i64 + 1;
        let s = self.fe.dec(sk, ct, tau)?;
        Some((self.size as i64 - s) / 2)
    }
}

/// Helper: random boolean using ark_std rng
fn rand_bit(rng: &mut impl ark_std::rand::RngCore) -> bool {
    use ark_std::rand::Rng;
    rng.gen_bool(0.5)
}


fn benchmark(n: usize, trials: usize) {
    use rand::{Rng, SeedableRng};
    use rand::rngs::StdRng;

    println!("\n{}", "=".repeat(60));
    println!("n = {}, trials = {}", n, trials);
    println!("{}", "=".repeat(60));

    // ── PiH ──────────────────────────────────────────────────────
    println!("\n[PiH]");

    // Setup
    let t = Instant::now();
    for _ in 0..trials {
        let mut pih = PiH::new(n);
        pih.setup();
    }
    println!("  Setup  : {:>10.3} ms/op", t.elapsed().as_secs_f64() * 1000.0 / trials as f64);

    // Build one scheme for the remaining operations
    let mut pih = PiH::new(n);
    pih.setup();

    let mut rng = StdRng::from_entropy();
    let b: Vec<u8>  = (0..n).map(|_| rng.gen_range(0..=1u8)).collect();
    let bp: Vec<u8> = (0..n).map(|_| rng.gen_range(0..=1u8)).collect();

    // Enroll
    let t = Instant::now();
    for _ in 0..trials {
        pih.enroll(&b).unwrap();
    }
    println!("  Enroll : {:>10.3} ms/op", t.elapsed().as_secs_f64() * 1000.0 / trials as f64);

    // Probe
    let t = Instant::now();
    for _ in 0..trials {
        pih.probe(&bp).unwrap();
    }
    println!("  Probe  : {:>10.3} ms/op", t.elapsed().as_secs_f64() * 1000.0 / trials as f64);

    // Comp (pre-generate em/pm outside the loop)
    let em = pih.enroll(&b).unwrap();
    let pm = pih.probe(&bp).unwrap();
    // Comp requires owned values — regenerate each trial
    let t = Instant::now();
    for _ in 0..trials {
        let em_i = pih.enroll(&b).unwrap();
        let pm_i = pih.probe(&bp).unwrap();
        pih.comp(&em_i, &pm_i).unwrap();
    }
    let total_ms = t.elapsed().as_secs_f64() * 1000.0 / trials as f64;
    // Subtract Enroll+Probe cost to isolate Comp
    let enroll_ms = {
        let t = Instant::now();
        for _ in 0..trials { pih.enroll(&b).unwrap(); }
        t.elapsed().as_secs_f64() * 1000.0 / trials as f64
    };
    let probe_ms = {
        let t = Instant::now();
        for _ in 0..trials { pih.probe(&bp).unwrap(); }
        t.elapsed().as_secs_f64() * 1000.0 / trials as f64
    };
    println!("  Comp   : {:>10.3} ms/op", total_ms - enroll_ms - probe_ms);
    let _ = (em, pm); // suppress unused warning

    // ── PiHC ─────────────────────────────────────────────────────
    println!("\n[PiHC]");

    // Setup
    let t = Instant::now();
    for _ in 0..trials {
        let mut pihc = PiHC::new(n);
        pihc.setup();
    }
    println!("  Setup  : {:>10.3} ms/op", t.elapsed().as_secs_f64() * 1000.0 / trials as f64);

    let mut pihc = PiHC::new(n);
    pihc.setup();

    // Enroll
    let t = Instant::now();
    for _ in 0..trials {
        pihc.enroll(&b).unwrap();
    }
    println!("  Enroll : {:>10.3} ms/op", t.elapsed().as_secs_f64() * 1000.0 / trials as f64);

    // Probe
    let t = Instant::now();
    for _ in 0..trials {
        pihc.probe(&bp).unwrap();
    }
    println!("  Probe  : {:>10.3} ms/op", t.elapsed().as_secs_f64() * 1000.0 / trials as f64);

    // Comp
    let t = Instant::now();
    for _ in 0..trials {
        let em_i = pihc.enroll(&b).unwrap();
        let pm_i = pihc.probe(&bp).unwrap();
        pihc.comp(&em_i, &pm_i).unwrap();
    }
    let total_ms = t.elapsed().as_secs_f64() * 1000.0 / trials as f64;
    let enroll_ms = {
        let t = Instant::now();
        for _ in 0..trials { pihc.enroll(&b).unwrap(); }
        t.elapsed().as_secs_f64() * 1000.0 / trials as f64
    };
    let probe_ms = {
        let t = Instant::now();
        for _ in 0..trials { pihc.probe(&bp).unwrap(); }
        t.elapsed().as_secs_f64() * 1000.0 / trials as f64
    };
    println!("  Comp   : {:>10.3} ms/op", total_ms - enroll_ms - probe_ms);
}

fn report_sizes(n: usize) {
    use rand::{Rng, SeedableRng};
    use rand::rngs::StdRng;
    let mut rng = StdRng::seed_from_u64(42);
    let b:  Vec<u8> = (0..n).map(|_| rng.gen_range(0..=1u8)).collect();
    let bp: Vec<u8> = (0..n).map(|_| rng.gen_range(0..=1u8)).collect();

    println!("\n{}", "=".repeat(60));
    println!("Size report  (n = {})", n);
    println!("{}", "=".repeat(60));

    // ── PiH ──
    let mut pih = PiH::new(n);
    let msk = pih.setup();

    // esk = psk = msk
    let msk_bytes = msk.byte_size();
    println!("\n[PiH]");
    println!("  esk (= psk = msk) : {} bytes  ({:.2} KB)", msk_bytes, msk_bytes as f64 / 1024.0);

    // csk for PiH holds only pp (empty) — real cost is the msk reference, report as 0
    println!("  csk (pp only)     : 0 bytes  (holds reference to msk)");

    let em = pih.enroll(&b).unwrap();
    let pm = pih.probe(&bp).unwrap();
    println!("  em  (SecretKey)   : {} bytes  ({:.2} KB)", em.byte_size(), em.byte_size() as f64 / 1024.0);
    println!("  pm  (Ciphertext)  : {} bytes  ({:.2} KB)", pm.byte_size(), pm.byte_size() as f64 / 1024.0);

    // ── PiHC ──
    let mut pihc = PiHC::new(n);
    pihc.setup();
    let msk_pihc = pihc.msk.as_ref().unwrap();

    // csk holds pp + n check SecretKeys
    let csk_bytes = msk_pihc.byte_size()
        + pihc.check_keys.iter().map(|sk| sk.byte_size()).sum::<usize>();

    println!("\n[PiHC]");
    println!("  esk (= psk = msk) : {} bytes  ({:.2} KB)", msk_pihc.byte_size(), msk_pihc.byte_size() as f64 / 1024.0);
    println!("  csk (pp + {} sks) : {} bytes  ({:.2} KB)", n, csk_bytes, csk_bytes as f64 / 1024.0);

    let em_c = pihc.enroll(&b).unwrap();
    let pm_c = pihc.probe(&bp).unwrap();
    println!("  em  (SecretKey)   : {} bytes  ({:.2} KB)", em_c.byte_size(), em_c.byte_size() as f64 / 1024.0);
    println!("  pm  (Ciphertext)  : {} bytes  ({:.2} KB)", pm_c.byte_size(), pm_c.byte_size() as f64 / 1024.0);

    // ── Element sizes for reference ──
    println!("\n[Element sizes for reference]");
    println!("  G1 compressed : {} bytes", G1Projective::generator().byte_size());
    println!("  G2 compressed : {} bytes", G2Projective::generator().byte_size());
    println!("  Fr scalar     : {} bytes", Fr::one().byte_size());
}

fn run_demo(n: usize) {
    use rand::{Rng, SeedableRng};
    use rand::rngs::StdRng;
    let mut rng = StdRng::from_entropy();

    let b:  Vec<u8> = (0..n).map(|_| rng.gen_range(0..=1u8)).collect();
    let bp: Vec<u8> = (0..n).map(|_| rng.gen_range(0..=1u8)).collect();
    let hd = hamming_distance(&b, &bp);

    println!("b  = {:?}", b);
    println!("b' = {:?}", bp);
    println!("True HD = {}", hd);

    println!("\n--- PiH ---");
    let mut pih = PiH::new(n);
    pih.setup();
    let em = pih.enroll(&b).unwrap();
    let pm = pih.probe(&bp).unwrap();
    match pih.comp(&em, &pm) {
        Some(z) => println!("PiH  HD = {}", z),
        None    => println!("PiH  Decryption failed"),
    }

    println!("\n--- PiHC ---");
    let mut pihc = PiHC::new(n);
    pihc.setup();
    let em_c = pihc.enroll(&b).unwrap();
    let pm_c = pihc.probe(&bp).unwrap();
    match pihc.comp(&em_c, &pm_c) {
        Some(z) => println!("PiHC HD = {}", z),
        None    => println!("PiHC Decryption failed / verification fault"),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args.get(1).map(String::as_str).unwrap_or("help");

    match mode {
        "speed" => {
            let configs: &[(usize, usize)] = &[
                (32,  10),
                (64,  10),
                (128, 10),
                (256, 10),
                (512, 10),
                (1024, 10),
            ];
            for &(n, trials) in configs {
                benchmark(n, trials);
            }
        }
        "sizes" => {
            for n in [32, 64, 128, 256, 512, 1024] {
                report_sizes(n);
            }
        }
        "run" => {
            // Normal correctness check
            let n: usize = args.get(2)
                .and_then(|s| s.parse().ok())
                .unwrap_or(8);
            run_demo(n);
        }
        _ => {
            println!("Usage:");
            println!("  cargo run --release -- speed   # timing benchmarks");
            println!("  cargo run --release -- sizes   # byte size report");
            println!("  cargo run --release -- run [n] # correctness demo");
        }
    }
}
