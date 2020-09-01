use algebra::{bls12_381::{Fr, G1Affine, G1Projective},
ProjectiveCurve
};
use algebra_core::{AffineCurve, msm::VariableBaseMSM, Zero, One, PrimeField,
bytes::{ToBytes},to_bytes, fields::Field};
use rand::{thread_rng,Rng};
use sha2::{Sha256, Digest};

use std::time::{Instant};


// The Common Reference String (CRS) is available to both the prover and verifier and allows the verifier to
// verify and make claims about committed values.
#[derive(Clone)]
pub struct CrsStruct {
    // Key used to generate proofs.
    pub crs_g: Vec<G1Affine>,
    pub crs_h: Vec<G1Affine>,
    pub u: G1Affine,
    pub crs_se1: G1Affine,
    pub crs_se2: G1Affine,
    pub crs_g_prod_ell: G1Projective,
    pub crs_g_prod_n: G1Projective,
    pub crs_gh: Vec<G1Affine>,
}

pub struct ShuffleProofStruct {
    pub g_m: G1Affine,
    pub g_a: G1Affine,
    pub proof_gprod: GprodProofStruct,
    pub g_r: G1Affine,
    pub g_s: G1Affine,
    pub g_t: G1Affine,
    pub g_u: G1Affine,
    pub proof_sameexp: SameexpProofStruct,
    pub proof_gpme: GpmeProofStruct,
}

pub struct GprodProofStruct {
    pub g_b: G1Affine,
    pub blinder: Fr,
    //pub proof_inner: GprodInnerProofStruct,
}

pub struct GprodProverInfoStruct {
    pub crs_h_scaled: Vec<G1Affine>,
    pub vec_b: Vec<Fr>,
    pub vec_c: Vec<Fr>,
    pub inner_prod: Fr,
}

pub struct GprodVerifierInfoStruct {
    pub vec_crs_h_exp: Vec<Fr>,
    pub g_b: G1Affine,
    pub g_c: G1Affine,
    pub inner_prod: Fr,
}

pub struct GpmeProofStruct {
    pub g_rgp: G1Affine,
    pub g_rme: G1Affine,
    pub blinder_gp: Fr,
    pub g_mebl1: G1Affine,
    pub g_mebl2: G1Affine,
    pub proof: Vec<[G1Affine; 10]>,
    pub b_final: Fr,
    pub c_final: Fr,
    pub a_final: Fr,
}

pub struct SameexpProofStruct {
    pub g_r1: G1Affine,
    pub g_r2: G1Affine,
    pub u1: Fr,
    pub u2: Fr,
    pub u3: Fr,
}

#[derive(Clone)]
pub struct FinalExpStruct {
    base: Vec<G1Affine>,
    exponents: Vec<Fr>,
}

pub fn hash_values(hash_input: Vec<u8>) -> Vec<u8> {
    let mut hasher = Sha256::new();
    hasher.update(hash_input);
    let current_hash = hasher.finalize();
    current_hash.to_vec()
}

pub fn get_challenge_from_current_hash(current_hash: &Vec<u8>) -> Fr {

    //The from_random_bytes function from zexe requires a 256 byte! array as input.
    //Filling extra data with zeros
    let mut current_hash_cp: Vec<u8> = current_hash.to_vec();

    //Sometimes x is None.  Hash again if this happens.
    let y = loop {
        let mut m = [0u8; 256];
        for i in 0..32 {
            m[i] = current_hash_cp[i];
        }
        let x = Fr::from_random_bytes(&m);
        if x != None {
            break x;
        }
        current_hash_cp = hash_values(current_hash_cp);
    };

    let z = y.unwrap();
    z
}

pub fn get_inner_prod(a: &Vec<Fr>, b: &Vec<Fr>) -> Fr {
    let mut c: Fr = Fr::zero();
    for i in 0..a.len() {
        c += a[i] * b[i];
    }
    c
}

pub fn add_to_final_expo(mut final_exps: FinalExpStruct, base_input: G1Affine, exponents_input: Fr) -> FinalExpStruct {
    final_exps.base.push(base_input);
    final_exps.exponents.push(exponents_input);
    final_exps
}

/// Totally insecure setup function.  Need to directly hash to curve to make secure.
pub fn setup(n: usize, num_blinders: usize) -> CrsStruct{
    let mut rng = thread_rng();

    let generator = G1Affine::prime_subgroup_generator();

    let mut c1: Vec<G1Affine>=Vec::new();
    let mut c2: Vec<G1Affine>=Vec::new();

    for _i in 0..n {
        let alpha1: Fr = rng.gen();
        let alpha2: Fr = rng.gen();
        c1.push( generator.mul(alpha1).into_affine() );
        c2.push( generator.mul(alpha2).into_affine() );
    }

    let alpha: Fr = rng.gen();
    let c3: G1Affine = generator.mul(alpha).into_affine();

    let mut c4 = c1[0];
    for i in 1..(n-num_blinders) {
        c4 += &c1[i];
    }

    let mut c4n = c4;
    for i in 0..num_blinders {
        c4n += &c1[n - num_blinders + i];
    }

    let mut c5: Vec<G1Affine> = Vec::new();
    c5.extend(& c1);
    c5.extend(& c2);

    let alpha1: Fr = rng.gen();
    let alpha2: Fr = rng.gen();
    let sameexp1 = generator.mul(alpha1).into_affine();
    let sameexp2 = generator.mul(alpha2).into_affine();

    let crs = CrsStruct {
        crs_g: c1,
        crs_h: c2,
        u: c3,
        crs_se1: sameexp1,
        crs_se2: sameexp2,
        crs_g_prod_ell: c4.into_projective(),
        crs_g_prod_n: c4n.into_projective(),
        crs_gh: c5,
    };

    crs
}

pub fn prove(crs: CrsStruct, ciph_r: &Vec<G1Affine>, ciph_s: &Vec<G1Affine>,
mut ciph_t: Vec<G1Affine>, mut ciph_u: Vec<G1Affine>, vec_shuffle: Vec<u32>, r: Fr,
ell: usize, n: usize, logn: usize)
-> ShuffleProofStruct {

    let mut rng = thread_rng();
    let num_blinders: usize = n - ell;

    let mut hash_input = to_bytes!(crs.u).unwrap();
    for i in 0..ell {
        hash_input.append(&mut to_bytes!(ciph_r[i]).unwrap());
        hash_input.append(&mut to_bytes!(ciph_s[i]).unwrap());
        hash_input.append(&mut to_bytes!(ciph_t[i]).unwrap());
        hash_input.append(&mut to_bytes!(ciph_u[i]).unwrap());
    }
    let mut current_hash = hash_values(hash_input);

    let mut vec_m: Vec<Fr> = Vec::new();
    for i in 0..ell {
        let mut mi = Fr::zero();
        for _j in 0..(vec_shuffle[i] as usize) {
            mi = mi + Fr::one();
        }
        vec_m.push(mi);
    }
    for _i in 0..num_blinders {
        vec_m.push(rng.gen());
    }

    let vec_m_formatted = vec_m.iter().map(|x| x.into_repr()).collect::<Vec<_>>();
    let g_m = VariableBaseMSM::multi_scalar_mul(crs.crs_g.as_slice(), vec_m_formatted.as_slice()).into_affine();

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(g_m).unwrap());
    current_hash = hash_values(hash_input);

    let mut vec_a: Vec<Fr> = Vec::new();
    for _i in 0..ell {
        vec_a.push(get_challenge_from_current_hash(&current_hash));
        current_hash = hash_values(current_hash);
    }

    let mut vec_a_shuffled: Vec<Fr> = Vec::new();
    for i in 0..ell {
        vec_a_shuffled.push(vec_a[vec_shuffle[i] as usize]);
    }
    for _i in 0..num_blinders {
        vec_a_shuffled.push(rng.gen());
    }

    let vec_formatted = vec_a_shuffled.iter().map(|x| x.into_repr()).collect::<Vec<_>>();
    let g_a = VariableBaseMSM::multi_scalar_mul(crs.crs_g.as_slice(), vec_formatted.as_slice()).into_affine();

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(g_a).unwrap());
    current_hash = hash_values(hash_input);

    let chal_alpha = get_challenge_from_current_hash(&current_hash);
    current_hash = hash_values(current_hash);
    let chal_beta = get_challenge_from_current_hash(&current_hash);

    let mut vec_gprod: Vec<Fr> = Vec::new();
    for i in 0..n {
        vec_gprod.push(vec_a_shuffled[i] + vec_m[i] * chal_alpha + chal_beta);
    }

    let mut gprod = Fr::one();
    for i in 0..ell {
        gprod *= vec_gprod[i];
    }

    let (current_hash, proof_gprod, gprod_prover_info) = gprod_prove(current_hash, &crs, gprod, vec_gprod, ell, n);

    let vec_formatted = vec_a.iter().map(|x| x.into_repr()).collect::<Vec<_>>();
    let g_r = VariableBaseMSM::multi_scalar_mul(ciph_r.as_slice(), vec_formatted.as_slice()).into_affine();
    let g_s = VariableBaseMSM::multi_scalar_mul(ciph_s.as_slice(), vec_formatted.as_slice()).into_affine();

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(g_a).unwrap());
    hash_input.append(&mut to_bytes!(g_r).unwrap());
    hash_input.append(&mut to_bytes!(g_s).unwrap());
    let mut current_hash = hash_values(hash_input);

    let mut vec_gamma: Vec<Fr> = Vec::new();
    let mut vec_delta: Vec<Fr> = Vec::new();
    for _i in 0..num_blinders {
        current_hash = hash_values(current_hash);
        vec_gamma.push( get_challenge_from_current_hash(&current_hash) );
        current_hash = hash_values(current_hash);
        vec_delta.push( get_challenge_from_current_hash(&current_hash) );
    }

    let mut blinder_se1: Fr = Fr::zero();
    let mut blinder_se2: Fr = Fr::zero();
    for i in 0..num_blinders {
        blinder_se1 += vec_gamma[i] * vec_a_shuffled[ell + i];
        blinder_se2 += vec_delta[i] * vec_a_shuffled[ell + i];
    }

    let g_t = (g_r.mul(r) + crs.crs_se1.mul(blinder_se1) ).into_affine();
    let g_u = (g_s.mul(r) + crs.crs_se2.mul(blinder_se2) ).into_affine();


    let (current_hash, proof_sameexp) = sameexp_prove(current_hash, g_r, g_s, crs.crs_se1,
        crs.crs_se2, g_t, g_u, r, blinder_se1, blinder_se2);

    for i in 0..num_blinders {
        ciph_t.push(crs.crs_se1.mul(vec_gamma[i]).into_affine());
        ciph_u.push(crs.crs_se2.mul(vec_delta[i]).into_affine());
    }

    let (_current_hash, proof_gpme) = gprod_and_multiexp_prove(current_hash, crs, gprod_prover_info.crs_h_scaled,
        gprod_prover_info.vec_b, gprod_prover_info.vec_c, gprod_prover_info.inner_prod,
    ciph_t.to_vec(), ciph_u.to_vec(), vec_a_shuffled, n, logn);

    let proof_shuffle = ShuffleProofStruct {
        g_m: g_m,
        g_a: g_a,
        proof_gprod: proof_gprod,
        g_r: g_r,
        g_s: g_s,
        g_t: g_t,
        g_u: g_u,
        proof_sameexp: proof_sameexp,
        proof_gpme: proof_gpme,
    };

    proof_shuffle

}

pub fn gprod_prove(mut current_hash: Vec<u8>, crs: &CrsStruct, gprod: Fr,
    vec_a: Vec<Fr>, ell: usize, n: usize)
    -> (Vec<u8>, GprodProofStruct, GprodProverInfoStruct)
    {

    let mut rng = thread_rng();
    let num_blinders: usize = n - ell;

    let mut vec_b: Vec<Fr> = Vec::new();
    let mut bi: Fr = Fr::one();
    for i in 0..ell {
        vec_b.push(bi);
        bi = bi * vec_a[i + 1];
    }
    for _i in 0..num_blinders {
        vec_b.push(rng.gen());
    }

    let vec_b_formatted = vec_b.iter().map(|x| x.into_repr()).collect::<Vec<_>>();
    let g_b = VariableBaseMSM::multi_scalar_mul(crs.crs_g.as_slice(), vec_b_formatted.as_slice()).into_affine();

    let mut blinder: Fr = Fr::zero();
    for i in 0..num_blinders {
        blinder += vec_a[ell + i] * vec_b[ell +i];
    }


    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(gprod).unwrap());
    hash_input.append(&mut to_bytes!(blinder).unwrap());
    hash_input.append(&mut to_bytes!(g_b).unwrap());


    current_hash = hash_values(hash_input);

    let chal_x = get_challenge_from_current_hash(&current_hash);
    let chal_inv_x = chal_x.inverse().unwrap();

    let mut vec_c: Vec<Fr> = Vec::new();

    let mut pow_x = chal_x;
    let mut pow_x2 = Fr::one();
    for i in 0..(ell-1) {
        vec_c.push(vec_a[i+1] * pow_x - pow_x2);
        pow_x = pow_x * chal_x;
        pow_x2 = pow_x2 * chal_x;
    }

    vec_c.push(vec_a[0] * pow_x - pow_x2);

    pow_x = pow_x * chal_x;
    for i in 0..num_blinders {
        vec_c.push(vec_a[ell + i] * pow_x);
    }

    let mut crs_h: Vec<G1Affine> = Vec::new();
    let mut pow_inv_x = chal_inv_x;
    for i in 0..(ell-1) {
        crs_h.push(crs.crs_g[i+1].mul(pow_inv_x).into_affine());
        pow_inv_x = pow_inv_x * chal_inv_x;
    }

    crs_h.push(crs.crs_g[0].mul(pow_inv_x).into_affine());

    pow_inv_x = pow_inv_x * chal_inv_x;
    for i in 0..num_blinders {
        crs_h.push(crs.crs_g[ell + i].mul(pow_inv_x).into_affine())
    }

    let inner_prod = blinder * chal_x.pow([(ell + 1) as u64]) + gprod * chal_x.pow([ell as u64]) - Fr::one();

    let proof_gprod = GprodProofStruct {
        g_b: g_b,
        blinder: blinder,
    };

    let gprod_prover_info = GprodProverInfoStruct {
        crs_h_scaled: crs_h,
        vec_b: vec_b,
        vec_c: vec_c,
        inner_prod: inner_prod,
    };

    (current_hash, proof_gprod, gprod_prover_info)
}

pub fn sameexp_prove(mut current_hash: Vec<u8>, g_1: G1Affine, g_2: G1Affine,
    h_1: G1Affine, h_2: G1Affine, y_1: G1Affine,
y_2: G1Affine, r: Fr, bl1: Fr, bl2: Fr) -> (Vec<u8>, SameexpProofStruct) {
    let mut rng = thread_rng();

    let s1: Fr = rng.gen();
    let s2: Fr = rng.gen();
    let s3: Fr = rng.gen();
    let g_r1: G1Affine = (g_1.mul(s1) + h_1.mul(s2)).into_affine();
    let g_r2: G1Affine = (g_2.mul(s1) + h_2.mul(s3)).into_affine();

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(g_1).unwrap());
    hash_input.append(&mut to_bytes!(g_2).unwrap());
    hash_input.append(&mut to_bytes!(y_1).unwrap());
    hash_input.append(&mut to_bytes!(y_2).unwrap());
    hash_input.append(&mut to_bytes!(g_r1).unwrap());
    hash_input.append(&mut to_bytes!(g_r2).unwrap());

    current_hash = hash_values(hash_input);
    let chal_x = get_challenge_from_current_hash(&current_hash);

    let u1: Fr = s1 + chal_x * r;
    let u2: Fr = s2 + chal_x * bl1;
    let u3: Fr = s3 + chal_x * bl2;

    let proof_sameexp = SameexpProofStruct {
        g_r1: g_r1,
        g_r2: g_r2,
        u1: u1,
        u2: u2,
        u3: u3,
    };

    (current_hash, proof_sameexp)
}

pub fn gprod_and_multiexp_prove(mut current_hash: Vec<u8>, mut crs: CrsStruct, mut crs_h_scaled: Vec<G1Affine>,
    mut vec_b: Vec<Fr>, mut vec_c: Vec<Fr>, mut inner_prod: Fr,
mut ciph_t: Vec<G1Affine>, mut ciph_u: Vec<G1Affine>, mut vec_exp: Vec<Fr>, n: usize, logn: usize)
-> (Vec<u8>, GpmeProofStruct) {

    let mut rng = thread_rng();
    let mut vec_rgp: Vec<Fr> = Vec::new();
    let mut vec_rme: Vec<Fr> = Vec::new();

    for _i in 0..n {
        vec_rgp.push(rng.gen());
        vec_rme.push(rng.gen());
    }

    let vec_formatted = vec_rgp.iter().map(|x| x.into_repr()).collect::<Vec<_>>();
    let g_rgp = VariableBaseMSM::multi_scalar_mul(crs_h_scaled.as_slice(), vec_formatted.as_slice()).into_affine();
    let blinder_gp = get_inner_prod(&vec_b, &vec_rgp);

    let vec_formatted = vec_rme.iter().map(|x| x.into_repr()).collect::<Vec<_>>();
    let g_rme = VariableBaseMSM::multi_scalar_mul(crs.crs_g.as_slice(), vec_formatted.as_slice()).into_affine();

    let g_mebl1 = VariableBaseMSM::multi_scalar_mul(ciph_t.as_slice(), vec_formatted.as_slice()).into_affine();
    let g_mebl2 = VariableBaseMSM::multi_scalar_mul(ciph_u.as_slice(), vec_formatted.as_slice()).into_affine();

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(g_rgp).unwrap());
    hash_input.append(&mut to_bytes!(blinder_gp).unwrap());
    hash_input.append(&mut to_bytes!(g_rme).unwrap());
    hash_input.append(&mut to_bytes!(g_mebl1).unwrap());
    hash_input.append(&mut to_bytes!(g_mebl2).unwrap());

    current_hash = hash_values(hash_input);
    let chal_x = get_challenge_from_current_hash(&current_hash);

    inner_prod += blinder_gp * chal_x;

    for i in 0..n {
        vec_c[i] += vec_rgp[i] * chal_x;
        vec_exp[i] += vec_rme[i] * chal_x;
    }

    let mut hash_input = current_hash;
    current_hash = hash_values(hash_input);
    let chal_x = get_challenge_from_current_hash(&current_hash);

    crs.u = crs.u.mul(chal_x).into_affine();

    let mut crs_h = crs.crs_g.clone();

    let mut proof: Vec<[G1Affine; 10]> = Vec::new();
    let mut current_n: usize = n;
    for _j in 0..logn {
        current_n = ( (current_n as u32) / 2) as usize;
        println!("current_n = {}", current_n);

        let zlgp = get_inner_prod(&vec_b[current_n..].to_vec(), &vec_c[..current_n].to_vec());
        let zrgp = get_inner_prod(&vec_b[..current_n].to_vec(), &vec_c[current_n..].to_vec());

        //let base = &mut ciph_t[current_n..].to_vec();
        let vec_formatted = vec_exp[..current_n].iter().map(|x| x.into_repr()).collect::<Vec<_>>();
        let g_zlme1 = VariableBaseMSM::multi_scalar_mul(&ciph_t[current_n..], vec_formatted.as_slice()).into_affine();

        //let base = &mut ciph_u[current_n..].to_vec();
        let g_zlme2 = VariableBaseMSM::multi_scalar_mul(&ciph_u[current_n..], vec_formatted.as_slice()).into_affine();

        //let base = &mut ciph_t[..current_n].to_vec();
        let vec_formatted = vec_exp[current_n..].iter().map(|x| x.into_repr()).collect::<Vec<_>>();
        let g_zrme1 = VariableBaseMSM::multi_scalar_mul(&ciph_t[..current_n], vec_formatted.as_slice()).into_affine();

        //let base = &mut ciph_u[..current_n].to_vec();
        let g_zrme2 = VariableBaseMSM::multi_scalar_mul(&ciph_u[..current_n], vec_formatted.as_slice()).into_affine();

        let base = &mut crs.crs_g[..current_n].to_vec();
        let vec_formatted = vec_b[current_n..].iter().map(|x| x.into_repr()).collect::<Vec<_>>();
        let mut g_clgpb = VariableBaseMSM::multi_scalar_mul(base.as_slice(), vec_formatted.as_slice()).into_affine();
        g_clgpb = g_clgpb + crs.u.mul(zlgp).into_affine();

        let base = &mut crs_h_scaled[current_n..].to_vec();
        let vec_formatted = vec_c[..current_n].iter().map(|x| x.into_repr()).collect::<Vec<_>>();
        let g_clgpc = VariableBaseMSM::multi_scalar_mul(base.as_slice(), vec_formatted.as_slice()).into_affine();

        let base = &mut crs.crs_g[current_n..].to_vec();
        let vec_formatted = vec_b[..current_n].iter().map(|x| x.into_repr()).collect::<Vec<_>>();
        let mut g_crgpb = VariableBaseMSM::multi_scalar_mul(base.as_slice() , vec_formatted.as_slice()).into_affine();
        g_crgpb = g_crgpb + crs.u.mul(zrgp).into_affine();

        let base = &mut crs_h_scaled[..current_n].to_vec();
        let vec_formatted = vec_c[current_n..].iter().map(|x| x.into_repr()).collect::<Vec<_>>();
        let g_crgpc = VariableBaseMSM::multi_scalar_mul(base.as_slice(), vec_formatted.as_slice()).into_affine();

        let base = &mut crs_h[current_n..].to_vec();
        let vec_formatted = vec_exp[..current_n].iter().map(|x| x.into_repr()).collect::<Vec<_>>();
        let g_clme = VariableBaseMSM::multi_scalar_mul(base.as_slice(), vec_formatted.as_slice()).into_affine();

        let base = &mut crs_h[..current_n].to_vec();
        let vec_formatted = vec_exp[current_n..].iter().map(|x| x.into_repr()).collect::<Vec<_>>();
        let g_crme = VariableBaseMSM::multi_scalar_mul(base.as_slice(), vec_formatted.as_slice()).into_affine();

        proof.push([g_zlme1, g_zlme2, g_zrme1, g_zrme2, g_clgpb, g_clgpc, g_crgpb, g_crgpc, g_clme, g_crme]);

        hash_input = current_hash;
        hash_input.append(&mut to_bytes!(g_zlme1).unwrap());
        hash_input.append(&mut to_bytes!(g_zlme2).unwrap());
        hash_input.append(&mut to_bytes!(g_zrme1).unwrap());
        hash_input.append(&mut to_bytes!(g_zrme2).unwrap());
        hash_input.append(&mut to_bytes!(g_clgpb).unwrap());
        hash_input.append(&mut to_bytes!(g_clgpc).unwrap());
        hash_input.append(&mut to_bytes!(g_crgpb).unwrap());
        hash_input.append(&mut to_bytes!(g_crgpc).unwrap());
        hash_input.append(&mut to_bytes!(g_clme).unwrap());
        hash_input.append(&mut to_bytes!(g_crme).unwrap());
        current_hash = hash_values(hash_input);

        let chal_x = get_challenge_from_current_hash(&current_hash);
        let chal_inv_x = chal_x.inverse().unwrap();

        for i in 0..current_n {
            crs.crs_g[i] = crs.crs_g[i] + crs.crs_g[current_n + i].mul(chal_inv_x).into_affine();
            crs_h_scaled[i] = crs_h_scaled[i] + crs_h_scaled[current_n + i].mul(chal_x).into_affine();
            vec_b[i] = vec_b[i] + chal_x * vec_b[current_n + i];
            vec_c[i] = vec_c[i] + chal_inv_x * vec_c[current_n + i];

            crs_h[i] = crs_h[i] + crs_h[current_n + i].mul(chal_x).into_affine();
            ciph_t[i] = ciph_t[i] + ciph_t[current_n + i].mul(chal_x).into_affine();
            ciph_u[i] = ciph_u[i] + ciph_u[current_n + i].mul(chal_x).into_affine();

            vec_exp[i] = vec_exp[i] + vec_exp[current_n + i] * chal_inv_x ;
        }

        crs.crs_g = crs.crs_g[..current_n].to_vec();
        crs_h_scaled = crs_h_scaled[..current_n].to_vec();
        vec_b = vec_b[..current_n].to_vec();
        vec_c = vec_c[..current_n].to_vec();

        crs_h = crs_h[..current_n].to_vec();
        ciph_t = ciph_t[..current_n].to_vec();
        ciph_u = ciph_u[..current_n].to_vec();
    }

    let proof_gpme = GpmeProofStruct {
        g_rgp: g_rgp,
        g_rme: g_rme,
        blinder_gp: blinder_gp,
        g_mebl1: g_mebl1,
        g_mebl2: g_mebl2,
        proof: proof,
        b_final: vec_b[0],
        c_final: vec_c[0],
        a_final: vec_exp[0],
    };

    (current_hash, proof_gpme)
}

pub fn verify(crs: CrsStruct, ciph_r: Vec<G1Affine>, ciph_s: Vec<G1Affine>,
mut ciph_t: Vec<G1Affine>, mut ciph_u: Vec<G1Affine>, proof_shuffle: ShuffleProofStruct,
ell: usize, n: usize, logn: usize)
-> bool {

    let num_blinders = n - ell;

    let now = Instant::now();
    let mut hash_input = to_bytes!(crs.u).unwrap();
    for i in 0..ell {
        hash_input.append(&mut to_bytes!(ciph_r[i]).unwrap());
        hash_input.append(&mut to_bytes!(ciph_s[i]).unwrap());
        hash_input.append(&mut to_bytes!(ciph_t[i]).unwrap());
        hash_input.append(&mut to_bytes!(ciph_u[i]).unwrap());
    }
    let mut current_hash = hash_values(hash_input);
    let new_now = Instant::now();
    println!("hashing time = {:?}", new_now.duration_since(now));    


    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(proof_shuffle.g_m).unwrap());
    current_hash = hash_values(hash_input);

    let mut vec_a: Vec<Fr> = Vec::new();
    for _i in 0..ell {
        vec_a.push(get_challenge_from_current_hash(&current_hash));
        current_hash = hash_values(current_hash);
    }

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(proof_shuffle.g_a).unwrap());
    let mut current_hash = hash_values(hash_input);

    let chal_alpha = get_challenge_from_current_hash(&current_hash);
    current_hash = hash_values(current_hash);
    let chal_beta = get_challenge_from_current_hash(&current_hash);

    let mut gprod = Fr::one();
    let mut field_i = Fr::zero();
    for i in 0..ell {
        gprod *= vec_a[i] + field_i * chal_alpha + chal_beta;
        field_i += Fr::one();
    }

    let g_a1 = proof_shuffle.g_a + (proof_shuffle.g_m.mul(chal_alpha) + (crs.crs_g_prod_n ).mul(chal_beta)).into_affine();

    let now = Instant::now();
    let (current_hash, gprod_verifier_info) = gprod_verify(current_hash, &crs, g_a1, gprod, proof_shuffle.proof_gprod, ell, n);
    let new_now = Instant::now();
    println!("gprod outer time = {:?}", new_now.duration_since(now));
//    check g_r and g_s correct in final exponentiation

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(proof_shuffle.g_a).unwrap());
    hash_input.append(&mut to_bytes!(proof_shuffle.g_r).unwrap());
    hash_input.append(&mut to_bytes!(proof_shuffle.g_s).unwrap());
    let mut current_hash = hash_values(hash_input);

    let mut vec_gamma: Vec<Fr> = Vec::new();
    let mut vec_delta: Vec<Fr> = Vec::new();
    for _i in 0..num_blinders {
        current_hash = hash_values(current_hash);
        vec_gamma.push( get_challenge_from_current_hash(&current_hash) );
        current_hash = hash_values(current_hash);
        vec_delta.push( get_challenge_from_current_hash(&current_hash) );
    }

    let now = Instant::now();
    let (current_hash, b1) = sameexp_verify(current_hash, proof_shuffle.g_r, proof_shuffle.g_s, crs.crs_se1,
        crs.crs_se2, proof_shuffle.g_t, proof_shuffle.g_u, proof_shuffle.proof_sameexp);
    let new_now = Instant::now();
    println!("sameexp time = {:?}", new_now.duration_since(now));

    let now = Instant::now();
    for i in 0..num_blinders {
        ciph_t.push(crs.crs_se1.mul(vec_gamma[i]).into_affine());
        ciph_u.push(crs.crs_se2.mul(vec_delta[i]).into_affine());
    }
    let new_now = Instant::now();
    println!("extra ciph time = {:?}", new_now.duration_since(now));

    let now = Instant::now();
    let (_current_hash, b2) = gprod_and_multiexp_verify(current_hash, crs, gprod_verifier_info.vec_crs_h_exp,
        gprod_verifier_info.g_b,
    gprod_verifier_info.g_c, gprod_verifier_info.inner_prod, ciph_t, ciph_u, proof_shuffle.g_a,
    proof_shuffle.g_t, proof_shuffle.g_u, proof_shuffle.proof_gpme,
    ciph_r, ciph_s, proof_shuffle.g_r, proof_shuffle.g_s, vec_a,
    ell, n, logn);
    let new_now = Instant::now();
    println!("inner product time = {:?}", new_now.duration_since(now));

    b1&b2
}

pub fn gprod_verify(mut current_hash: Vec<u8>, crs: &CrsStruct, g_a1: G1Affine, gprod: Fr,
    proof_gprod: GprodProofStruct, ell: usize, n:usize)
-> (Vec<u8>, GprodVerifierInfoStruct) {

    let num_blinders = n - ell;

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(gprod).unwrap());
    hash_input.append(&mut to_bytes!(proof_gprod.blinder).unwrap());
    hash_input.append(&mut to_bytes!(proof_gprod.g_b).unwrap());


    current_hash = hash_values(hash_input);

    let chal_x = get_challenge_from_current_hash(&current_hash);
    let chal_inv_x = chal_x.inverse().unwrap();


    let mut g_c = crs.crs_g_prod_ell.mul(-chal_inv_x).into_affine();
    g_c += &g_a1;


    let mut vec_crs_h_exp: Vec<Fr> = Vec::new();
    let mut pow_inv_x = chal_inv_x;
    vec_crs_h_exp.push(Fr::one());
    for _i in 1..ell {
        vec_crs_h_exp.push(pow_inv_x);
        pow_inv_x *= chal_inv_x;
    }

    vec_crs_h_exp[0] = pow_inv_x;
    pow_inv_x *= chal_inv_x;

    for _i in 0..num_blinders {
        vec_crs_h_exp.push(pow_inv_x);
    }

    let inner_prod = proof_gprod.blinder * chal_x.pow([(ell + 1) as u64]) + gprod * chal_x.pow([ell as u64]) - Fr::one();

    //let (current_hash, b) = gprod_verify_inner(current_hash, crs, vec_crs_h_exp, g_c, inner_prod, proof_gprod.proof_inner, ell, n, logn);

    let gprod_verifier_info = GprodVerifierInfoStruct {
        vec_crs_h_exp: vec_crs_h_exp,
        g_b: proof_gprod.g_b,
        g_c: g_c,
        inner_prod: inner_prod,
    };

    (current_hash, gprod_verifier_info)

    }


pub fn sameexp_verify(mut current_hash: Vec<u8>, g_1: G1Affine, g_2: G1Affine,
    h_1: G1Affine, h_2: G1Affine, y_1: G1Affine,
y_2: G1Affine, proof_sameexp: SameexpProofStruct) -> (Vec<u8>, bool) {
    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(g_1).unwrap());
    hash_input.append(&mut to_bytes!(g_2).unwrap());
    hash_input.append(&mut to_bytes!(y_1).unwrap());
    hash_input.append(&mut to_bytes!(y_2).unwrap());
    hash_input.append(&mut to_bytes!(proof_sameexp.g_r1).unwrap());
    hash_input.append(&mut to_bytes!(proof_sameexp.g_r2).unwrap());

    current_hash = hash_values(hash_input);
    let chal_x = get_challenge_from_current_hash(&current_hash);

    let g_expected: G1Affine = proof_sameexp.g_r1 + (y_1.mul(chal_x)
    + g_1.mul(- proof_sameexp.u1) + h_1.mul(- proof_sameexp.u2)).into_affine();
    let b1 = g_expected.infinity;

    let g_expected: G1Affine = proof_sameexp.g_r2 + (y_2.mul(chal_x)
    + g_2.mul(- proof_sameexp.u1) + h_2.mul(- proof_sameexp.u3)).into_affine();
    let b2 = g_expected.infinity;

    let b: bool = b1 & b2;

    (current_hash, b)

}

pub fn get_challenges_gpme_verify(mut current_hash: Vec<u8>, proof_gpme: &GpmeProofStruct, logn: usize)
-> Vec<Fr> {
    let mut challenges: Vec<Fr> = Vec::new();

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(proof_gpme.g_rgp).unwrap());
    hash_input.append(&mut to_bytes!(proof_gpme.blinder_gp).unwrap());
    hash_input.append(&mut to_bytes!(proof_gpme.g_rme).unwrap());
    hash_input.append(&mut to_bytes!(proof_gpme.g_mebl1).unwrap());
    hash_input.append(&mut to_bytes!(proof_gpme.g_mebl2).unwrap());

    current_hash = hash_values(hash_input);
    challenges.push( get_challenge_from_current_hash(&current_hash) );
    // let chal_zk = get_challenge_from_current_hash(&current_hash);

    let hash_input = current_hash;
    current_hash = hash_values(hash_input);
    challenges.push( get_challenge_from_current_hash(&current_hash) );

    for j in 0..logn {
        let mut hash_input = current_hash;
        for i in 0..10 {
            hash_input.append(&mut to_bytes!(proof_gpme.proof[j][i]).unwrap())
        }

        current_hash = hash_values(hash_input);
        challenges.push( get_challenge_from_current_hash(&current_hash) )
    }

    let mut hash_input = current_hash;
    hash_input.append(&mut to_bytes!(proof_gpme.b_final).unwrap()) ;
    hash_input.append(&mut to_bytes!(proof_gpme.c_final).unwrap());
    hash_input.append(&mut to_bytes!(proof_gpme.a_final).unwrap());
    current_hash = hash_values(hash_input);

    challenges.push(get_challenge_from_current_hash(&current_hash.to_vec()));
    current_hash = hash_values(current_hash);
    challenges.push(get_challenge_from_current_hash(&current_hash.to_vec()));
    current_hash = hash_values(current_hash);
    challenges.push(get_challenge_from_current_hash(&current_hash.to_vec()));
    current_hash = hash_values(current_hash);
    challenges.push(get_challenge_from_current_hash(&current_hash.to_vec()));
    current_hash = hash_values(current_hash);
    challenges.push(get_challenge_from_current_hash(&current_hash.to_vec()));
    current_hash = hash_values(current_hash);
    challenges.push(get_challenge_from_current_hash(&current_hash.to_vec()));
    challenges
}

pub fn gprod_and_multiexp_verify(current_hash: Vec<u8>, crs: CrsStruct, vec_crs_h_exp: Vec<Fr>,
g_b: G1Affine,
g_c: G1Affine, mut inner_prod: Fr, ciph_t: Vec<G1Affine>, ciph_u: Vec<G1Affine>, g_a: G1Affine,
g_t: G1Affine, g_u: G1Affine, proof_gpme: GpmeProofStruct,
ciph_r: Vec<G1Affine>, ciph_s: Vec<G1Affine>, g_r: G1Affine, g_s: G1Affine, vec_a: Vec<Fr>,
ell: usize, n: usize, logn: usize
) -> (Vec<u8>, bool) {

    let mut final_exps: FinalExpStruct = FinalExpStruct {
            base: Vec::new(),
            exponents: Vec::new(),
    };


    // challenges = [zk, u_scale, inner[0], ... , inner[logn - 1], veq1, veq2, veq3, veq4 ]
    let now = Instant::now();
    let challenges = get_challenges_gpme_verify(current_hash.clone(), &proof_gpme, logn);
    let new_now = Instant::now();
    println!("getting challenges time = {:?}", new_now.duration_since(now));

    // inverse challenges
    let now = Instant::now();
    let mut x_invs: Vec<Fr> = challenges[2..(logn+2)].to_vec();
    algebra_core::batch_inversion(&mut x_invs);
    let new_now = Instant::now();
    println!("inversion time = {:?}", new_now.duration_since(now));

    final_exps = add_to_final_expo(final_exps, g_r, - Fr::one());
    final_exps = add_to_final_expo(final_exps, g_s, - challenges[logn + 7]);
    for i in 0..vec_a.len() {
        final_exps = add_to_final_expo(final_exps, ciph_r[i], vec_a[i]);
        final_exps = add_to_final_expo(final_exps, ciph_s[i], challenges[logn + 7] * vec_a[i]);
    }

    inner_prod += proof_gpme.blinder_gp * challenges[0];

    //g_c = g_c + proof_gpme.g_rgp.mul(chal_zk);
    final_exps = add_to_final_expo(final_exps, g_c, - challenges[logn + 6]);
    final_exps = add_to_final_expo(final_exps, proof_gpme.g_rgp, - challenges[0] * challenges[logn + 6]);

    //g_t = g_t + proof_gpme.g_mebl1.mul(chal_zk);
    final_exps = add_to_final_expo(final_exps, g_t, - challenges[logn + 4]);
    final_exps = add_to_final_expo(final_exps, proof_gpme.g_mebl1, - challenges[logn + 4] * challenges[0]);

    //g_u = g_u + proof_gpme.g_mebl2.mul(chal_zk);
    final_exps = add_to_final_expo(final_exps, g_u, - challenges[logn + 5]);
    final_exps = add_to_final_expo(final_exps, proof_gpme.g_mebl2, - challenges[logn + 5] * challenges[0]);

    //g_a = g_a + proof_gpme.g_rme.mul(chal_zk);
    final_exps = add_to_final_expo(final_exps, g_a, - challenges[logn + 2]);
    final_exps = add_to_final_expo(final_exps, proof_gpme.g_rme, - challenges[logn + 2] * challenges[0]);

    // g_b = g_b + crs.u.mul(chal_uscale * b_final * c_final - chal_uscale * inner_prod)
    final_exps = add_to_final_expo(final_exps, g_b, - challenges[logn + 3]);
    final_exps = add_to_final_expo(final_exps, crs.u,
        challenges[1] * challenges[logn + 3] * proof_gpme.b_final * proof_gpme.c_final
        - challenges[logn + 3] * challenges[1] * inner_prod);

    let mut vec_crs_g_exp: Vec<Fr> = Vec::new();
    let mut vec_crs_h_shifted: Vec<Fr> = Vec::new();

    for _i in 0..n {
        vec_crs_g_exp.push(proof_gpme.b_final);
        vec_crs_h_shifted.push(Fr::one());
    }

    let mut current_n: usize = n;
    for j in 0..logn {
        current_n = ( (current_n as u32) / 2) as usize;


        let chal_x = challenges[2 + j];
        let chal_inv_x = x_invs[j];

        for i in 0..n {
            let bitstring = format!("{:b}", i);
            let mut bit_vec: Vec<char> = bitstring.chars().collect();
            bit_vec.reverse();
            while bit_vec.len() < logn {
                bit_vec.push('0');
            }

            if bit_vec[logn - j - 1] == '1' {
                vec_crs_g_exp[i] = vec_crs_g_exp[i] * chal_inv_x;
                vec_crs_h_shifted[i] = vec_crs_h_shifted[i] * chal_x;
            }
        }

        //[g_zlme1, g_zlme2, g_zrme1, g_zrme2, g_clgp, g_crgp, g_clme, g_crme]
        //[g_zlme1, g_zlme2, g_zrme1, g_zrme2, g_clgpb, g_clgpc, g_crgpb, g_crgpc, g_clme, g_crme]

        //g_b = proof_gpme.proof[j][4].mul(chal_x) + g_b + proof_gpme.proof[j][6].mul(chal_inv_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][4], - challenges[logn + 3] * chal_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][6], - challenges[logn + 3] * chal_inv_x);

        //g_c = proof_gpme.proof[j][5].mul(chal_x) + g_c + proof_gpme.proof[j][7].mul(chal_inv_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][5], - challenges[logn + 6] * chal_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][7], - challenges[logn + 6] * chal_inv_x);

        //g_t = proof_gpme.proof[j][0].mul(chal_x) + g_t + proof_gpme.proof[j][2].mul(chal_inv_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][0], - challenges[logn + 4] * chal_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][2], - challenges[logn + 4] * chal_inv_x);

        //g_u = proof_gpme.proof[j][1].mul(chal_x) + g_u + proof_gpme.proof[j][3].mul(chal_inv_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][1], - challenges[logn + 5] * chal_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][3], - challenges[logn + 5] * chal_inv_x);

        //g_a = proof_gpme.proof[j][8].mul(chal_x) + g_a + proof_gpme.proof[j][9].mul(chal_inv_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][8], - challenges[logn + 2] * chal_x);
        final_exps = add_to_final_expo(final_exps, proof_gpme.proof[j][9], - challenges[logn + 2] * chal_inv_x);

    }

    //    let b1 = (g_ciph_t_final.mul(- proof_gpme.exp_final) + g_t).into_affine().infinity;
    //    let b2 = (g_ciph_u_final.mul(- proof_gpme.exp_final) + g_u).into_affine().infinity;
    for i in 0..n {
        final_exps = add_to_final_expo(final_exps, ciph_t[i], challenges[logn + 4] * vec_crs_h_shifted[i]
            * proof_gpme.a_final);

        final_exps = add_to_final_expo(final_exps, ciph_u[i], challenges[logn + 5] * vec_crs_h_shifted[i]
                * proof_gpme.a_final);
    }


    let mut vec_crs_exp: Fr = challenges[logn + 3] * vec_crs_g_exp[0] +
    challenges[logn + 2] * vec_crs_h_shifted[0] * proof_gpme.a_final
    + challenges[logn + 6] * vec_crs_h_exp[0] * vec_crs_h_shifted[ell-1]*proof_gpme.c_final;

    final_exps = add_to_final_expo(final_exps, crs.crs_g[0], vec_crs_exp);

    for i in 1..ell {
        vec_crs_exp = challenges[logn + 3] * vec_crs_g_exp[i] +
        challenges[logn + 2] * vec_crs_h_shifted[i] * proof_gpme.a_final
        + challenges[logn + 6] * vec_crs_h_exp[i] * vec_crs_h_shifted[i-1]*proof_gpme.c_final;

        final_exps = add_to_final_expo(final_exps, crs.crs_g[i], vec_crs_exp);
    }

    for i in ell..n {
        vec_crs_exp = challenges[logn + 3] * vec_crs_g_exp[i] +
        challenges[logn + 2] * vec_crs_h_shifted[i] * proof_gpme.a_final
        + challenges[logn + 6] * vec_crs_h_exp[i] * vec_crs_h_shifted[i]*proof_gpme.c_final;

        final_exps = add_to_final_expo(final_exps, crs.crs_g[i], vec_crs_exp);
    }

    let now = Instant::now();
    let vec_formatted = final_exps.exponents.iter().map(|x| x.into_repr()).collect::<Vec<_>>();
    let g_expected: G1Affine = VariableBaseMSM::multi_scalar_mul(final_exps.base.as_slice(), vec_formatted.as_slice()).into_affine();
    let b3 = g_expected.infinity;
    let new_now = Instant::now();
    println!("final exponentiation time = {:?}", new_now.duration_since(now));

    (current_hash, b3)
}
