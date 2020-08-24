mod shuffle;

use shuffle::{setup, prove, verify};

use algebra::{bls12_381::{Fr, G1Affine}};
use algebra_core::{AffineCurve, curves::ProjectiveCurve};

use rand::{thread_rng,Rng};
use std::time::{Instant};

fn get_shuffle(ciph_r: &Vec<G1Affine>, ciph_s: &Vec<G1Affine>, ell: usize) ->
    (Vec<G1Affine>, Vec<G1Affine>, Vec<u32>, Fr)
 {
    let mut rng = thread_rng();

    let mut vec_leftover: Vec<u32> = Vec::new();
    for i in 0..ell {
        vec_leftover.push(i as u32);
    }

    let mut vec_shuffle: Vec<u32> = Vec::new();
    for i in 0..ell {
        let k = rng.gen_range(0, ell - i);
        vec_shuffle.push(vec_leftover[k]);
        vec_leftover.retain(|&x| x != vec_shuffle[i]);
    }


    let mut ciph_t: Vec<G1Affine> = Vec::new();
    let mut ciph_u: Vec<G1Affine> = Vec::new();
    let r: Fr = rng.gen();
    for i in 0..ell {
        ciph_t.push( ciph_r[vec_shuffle[i] as usize].mul(r).into_affine() );
        ciph_u.push( ciph_s[vec_shuffle[i] as usize].mul(r).into_affine() );
    }

    (ciph_t, ciph_u, vec_shuffle, r)
}


fn main() {
    let n: usize = 128;
    let ell: usize = n - 4;
    let logn: usize = 7;
    if (2 as u32).pow(logn as u32) != n as u32 {
        println!("Error, logn must equal log_2(n), should panic");
    }
    let mut rng = thread_rng();

    let now = Instant::now();
    let crs = setup(n, n - ell);
    let new_now = Instant::now();
    println!("crs time = {:?}", new_now.duration_since(now));

    let now = Instant::now();
    let mut ciph_r: Vec<G1Affine> = Vec::new();
    let mut ciph_s: Vec<G1Affine> = Vec::new();

    let generator = G1Affine::prime_subgroup_generator();
    for _i in 0..ell {
        let alpha1: Fr = rng.gen();
        let alpha2: Fr = rng.gen();
        ciph_r.push( generator.mul(alpha1).into_affine() );
        ciph_s.push( generator.mul(alpha2).into_affine() );
    }
    let new_now = Instant::now();
    println!("shuffle time = {:?}", new_now.duration_since(now));

    let (ciph_t, ciph_u, vec_shuffle, r) = get_shuffle(&ciph_r, &ciph_s, ell);

    let crs_cp = crs.clone();
    let ciph_t_cp = ciph_t.clone();
    let ciph_u_cp = ciph_u.clone();

    let now = Instant::now();
    let proof_shuffle = prove(crs_cp, &ciph_r, &ciph_s, ciph_t_cp, ciph_u_cp, vec_shuffle, r,
    ell, n, logn);
    let new_now = Instant::now();
    println!("proving time = {:?}", new_now.duration_since(now));

    let now = Instant::now();
    let crs_cp = crs.clone();
    let b = verify(crs_cp, ciph_r, ciph_s, ciph_t, ciph_u, proof_shuffle, ell, n, logn);
    let new_now = Instant::now();
    println!("Verification passes = {:?}", b);
    println!("verifying time = {:?}", new_now.duration_since(now));

}
