// aes.java
// Advanced Encryption Standard (AES) Implementation
// http://csrc.nist.gov/publications/fips/fips197/fips-197.pdf

// Criptografia 
// Facultat d'Informatica de Barcelona
// http://www.fib.upc.es

// Francesc Vendrell i Soler 
// March 2012

import java.math.BigInteger;
import java.util.Random;
import java.nio.ByteBuffer;

public class aes {

    /* *********************************** */
    /* MAIN VARIABLES CONSTANTS AND TABLES */
    /* *++++++++++++++++++++++++++++++++++ */

    // anti-log (exponentiation) table.
    private static final byte[] alog  = new byte[256];
    // log table.
    private static final byte[] log   = new byte[256];
    // inv table
    private static final byte[] inv   = new byte[256];
    // substitution table (sbox)
    private static final byte[] sbox  = new byte[256];
    // inverse substitution table (inv sbox)
    private static final byte[] invsb = new byte[256];
    // rcon x^i for key expansion
    private static final byte[] rcon  = new byte[11];
    // mix column matrix
    private static final byte  mix[][] = {{ 2,3,1,1 }, { 1,2,3,1 }, { 1,1,2,3 }, { 3,1,1,2 }};
    // inverse mix column matrix
    private static final byte  mix_inv[][] = {{ 0x0E,0x0B,0x0D,0x09 },{ 0x09,0x0E,0x0B,0x0D }, 
                                              { 0x0D,0x09,0x0E,0x0B },{ 0x0B,0x0D,0x09,0x0E }};   

    /* ******************************************* */
    /* STATIC CODE - INITIALIZATIONS AND CONSTANTS */
    /* ******************************************* */

    // Mask bytes for sbox and inverse sbox
    static final byte mask     = 0x1F;
    static final byte mask_inv = 0x4A; 

    // compute log, anti-log and mult. inverse tables using 0x03 as a generator
    static {
        int a,b;
        alog[0] = 1;
        log [0] = 0;
        // multiply by three in Rijndael's Galois field is simply a multiply 
        // by two exclusive ored with the value we are multiplying by.
        for(int i=1; i<256; i++) {
            a = (alog[i-1])<<1;
            // x2 reduced using AES irreducible polynomial 0x1b
            if((a&0x800) != 0) a ^= 0x1B;
            // log and antilog tables
            alog[i]           = (byte)(alog[i-1]^a);
            log[0xFF&alog[i]] = (byte)i;
        }
        // inv table
        inv[0] = 0;
        for(int i=1; i<256; i++) inv[i] = alog[255-(0xFF&log[i])];
    }

    // compute sbox and inverse sbox tables
    static {
        byte mask_j   , bits    , sum;
        byte mask_jinv, bits_inv, sum_inv;
        for(int i=0; i<256; i++) {
            bits=inv[i]; mask_j=mask; sum=0;
            bits_inv=(byte)(i^0x63); mask_jinv=mask_inv; sum_inv=0;
            for(int j=0; j<8; j++, bits>>=1, bits_inv>>=1) {
                if((1&bits)     == 1) sum     ^= mask_j; 
                if((1&bits_inv) == 1) sum_inv ^= mask_jinv; 
                // rotate mask bytes (cool ha!)
                mask_j    = (byte)((mask_j   <<1)|(0x01&(mask_j   >>7)));
                mask_jinv = (byte)((mask_jinv<<1)|(0x01&(mask_jinv>>7)));
            }
            sbox[i]  = (byte)(sum^0x63);
            invsb[i] = inv[0xFF&sum_inv]; 
        }
    }

    // x^i table (i=10 max when Nk=4 and Nr=10)
    static {
        int a;
        rcon[0]=1; rcon[1]=2;
        for(int i=2; i<=10; i++) {
            // muliply by 2
            a = (rcon[i-1]<<1);
            rcon[i] = (byte)a;
            // reduce modulus m(x) if necessary
            if((a&0x800) != 0) rcon[i] = (byte)(a^0x1b); 
        }
    }

    /* ************************* */
    /* MAIN METHODS - SIGNATURES */
    /* ************************* */
    
    public static byte[][][] keyExpansion(BigInteger K, int Nk, int Nr) {
        // compute keys
        byte W[][] = expandKey(K,Nk,Nr);
        // create result
        byte[][][] k_exp = new byte[Nr+1][4][4];
        for(int i=0; i<Nr+1; i++)
            for(int j=0; j<4; j++)
                for(int k=0; k<4; k++)
                    k_exp[i][k][j] = W[k][j+4*i];
        return k_exp;
    }
    
    public static byte[][][] invKeyExpansion(BigInteger K, int Nk, int Nr) {
        // compute keys
        byte[][] W = expandKey(K,Nk,Nr);
        // copy unchanged keys (first and last ones)
        byte[][][] k_exp = new byte[Nr+1][4][4];
        for(int i=0; i<4; i++) 
            for(int j=0; j<4; j++) {
                k_exp [0][j][i] = W[j][i];
                k_exp[Nr][j][i] = W[j][4*Nr+i]; 
            }
        // create result applying invMixColumn to keys from 1 to Nr
        for(int i=1; i<Nr; i++)
            for(int j=0; j<4; j++)
                for(int k=0; k<4; k++)
                    for(int r=0; r<4; r++)
                        k_exp[i][r][j] ^= prod(mix_inv[r][k],W[k][j+4*i]);
        return k_exp;
    }

    public static byte byteSub(byte subestat) {
        return sbox[0xFF&subestat];
    }
    
    public static byte invByteSub(byte subestat) {
        return invsb[0xFF&subestat];
    }

    public static byte[][] shiftRow(byte[][] estat) {
        return new byte[][] {
            { estat[0][0], estat[0][1], estat[0][2], estat[0][3] },
            { estat[1][1], estat[1][2], estat[1][3], estat[1][0] },
            { estat[2][2], estat[2][3], estat[2][0], estat[2][1] },
            { estat[3][3], estat[3][0], estat[3][1], estat[3][2] },
        };
    }
    
    public static byte[][] invShiftRow(byte[][] estat) {
        return new byte[][] {
            { estat[0][0], estat[0][1], estat[0][2], estat[0][3] },
            { estat[1][3], estat[1][0], estat[1][1], estat[1][2] },
            { estat[2][2], estat[2][3], estat[2][0], estat[2][1] },
            { estat[3][1], estat[3][2], estat[3][3], estat[3][0] },
        };
    }

    public static byte[][] mixColumn(byte[][] estat) {
        byte res[][] = new byte[4][4];
        for(int i=0; i<4; i++)
            for(int j=0; j<4; j++)
                for(int k=0; k<4; k++)
                    res[k][i] ^= prod(mix[k][j],estat[j][i]);
        return res;
    }
    
    public static byte[][] invMixColumn(byte[][] estat) {
        byte res[][] = new byte[4][4];
        for(int i=0; i<4; i++)
            for(int j=0; j<4; j++)
                for(int k=0; k<4; k++)
                    res[k][i] ^= prod(mix_inv[k][j],estat[j][i]);
        return res;
    }

    public static byte[][] addRoundKey(byte[][] estat, byte[][] Ki) {
        byte[][] res = new byte[4][4];
        for(int i=0; i<4; i++)
            for(int j=0; j<4; j++)
                res[j][i] = (byte)(estat[j][i]^Ki[j][i]);
        return res;
    }
    
    public static byte[][] rijndael(byte[][] estat, byte[][][] W, int Nk, int Nr) {
        // get initial key
        byte[][] key = get_key(0,W);
        byte[][] res = copy_state(estat);
        // add initial key
        res = addRoundKey(res,key);
        // apply cipher algorithm
        for(int i=1; i<Nr; i++) {
            // get key ki
            key = get_key(i,W);
            // apply operations
            res = addRoundKey(mixColumn(shiftRow(SubBytes(res))),key);
        }
        // get last key
        key = get_key(Nr,W);
        // omit mix column
        return  addRoundKey(shiftRow(SubBytes(res)),key);
    }
    
    public static byte[][] invRijndael(byte[][] estat, byte[][][] InvW, int Nk, int Nr) {
        // get initial key (last one)
        byte[][] key = get_key(Nr,InvW);
        byte[][] res = copy_state(estat);
        // add initial key
        res = addRoundKey(res,key);
        // apply decipher algorithm
        for(int i=Nr-1; i>0; i--) {
            // get key k(Nr-i)
            key = get_key(i,InvW);
            // apply operations        
            res = addRoundKey(invMixColumn(invShiftRow(invSubBytes(res))),key);
        }
        // get last key (first one)
        key = get_key(0,InvW);
        // omit mix column
        return addRoundKey(invShiftRow(invSubBytes(res)),key);
    }

    public static byte[] xifrarAES(byte[] M, BigInteger K, int Lk) {
        // compute Nk and Nr
        int Nr, Nk = Lk/32;
        if(Nk==4) Nr=10; else if(Nk==6) Nr=12; else Nr=14;
        // generate random IV number
        Random rand = new Random();
        byte[] IV   = new byte[16];
        rand.nextBytes(IV);
        // add random IV and pad message
        byte[] C = IVpadMessage(M,IV);
        // cipher padded plaintext 
        byte[][] estat = new byte[4][4];
        // first block of data is IV
        byte[][] prev  = get_block(C,0);
        // cipher plaintext to C
        for(int i=16; i<C.length; i+=16) {
            // get plaintext block and encrypt it
            estat = rijndael(xor(get_block(C,i),prev),keyExpansion(K,Nk,Nr),Nk,Nr);
            // replace plaintext with cipher text
            copy_block(estat,C,i);
            // next block
            prev = estat;
        }
        // return ciphertext
        return C;
    }

    public static byte[] desxifrarAES(byte[] C, BigInteger K, int Lk) {
        // get IV
        byte[][] prev = get_block(C,0);
        // compute Nk and Nr
        int Nk = Lk/32, n = C.length;
        int Nr; if(Nk==4) Nr=10; else if(Nk==6) Nr=12; else Nr=14;
        // loop that deciphers ciphertext data
        byte[][] next  = new byte[4][4];
        byte[][] estat = new byte[4][4];
        byte[] M       = new byte[n-16];
        for(int i=16; i<n; i+=16) {
            // get encrypted block
            next  = get_block(C,i);
            // decrypt block
            estat = xor(invRijndael(next,invKeyExpansion(K,Nk,Nr),Nk,Nr),prev);
            // copy block
            copy_block(estat,M,i-16);
            // next
            prev  = next;
        }
        // get size
        n-=16;
        ByteBuffer bb = ByteBuffer.wrap(new byte[] {M[n-8],M[n-7],M[n-6],M[n-5],M[n-4],M[n-3],M[n-2],M[n-1]});
        long size = bb.getLong()/8;
        // delete padded data
        // WARNING!!: it can fail if key is not correct, and data size are random bits, 
        byte[] plaintext = new byte[(int)(size)];
        for(int i=0; i<size; i++) plaintext[i] = M[i];
        // return decrypted text
        return plaintext;
    }

    /* ************************* */
    /* PRIVATE AUXILIARY METHODS */
    /* ************************* */

    private static byte prod(byte a, byte b) {
        if(a==0 || b==0) return 0;
        else return alog[((0xFF&log[0xFF&a])+(0xFF&log[0xFF&b]))%255];
    }
    
    private static byte[][] SubBytes(byte[][] state) {
        byte[][] res = new byte[4][4];
        for(int i=0; i<4; i++) 
            for(int j=0; j<4; j++)
                res[i][j] = byteSub(state[i][j]);
        return res;
    }
    
    private static byte[][] invSubBytes(byte[][] state) {
        byte[][] res = new byte[4][4];
        for(int i=0; i<4; i++) 
            for(int j=0; j<4; j++)
                res[i][j] = invByteSub(state[i][j]);
        return res;
    }

    private static byte[] SubWord(byte[] word) {
        byte res[] = new byte[4];
        for(int i=0; i<4; i++) 
            res[i] = byteSub(word[i]);
        return res;
    }

    private static byte[] RotWord(byte[] word) {
        byte[] res = new byte[4];
        byte b     = word[0];
        for(int i=1; i<4; i++) res[i-1] = word[i];
        res[3] = b;
        return res;
    }

    private static byte[] Rcon(int i) {
        byte[] exp = new byte[4];
        exp[0] = rcon[i-1];
        exp[1] = exp[2] = exp[3] = 0;
        return exp;
    }

    private static byte[] xor(byte[] w1, byte[] w2) {
        byte[] w = new byte[4];
        for(int i=0; i<4; i++)
            w[i] = (byte)(w1[i]^w2[i]);
        return w;
    }

    private static byte[][] xor(byte[][] w1, byte[][] w2) {
        byte[][] w = new byte[4][4];
        for(int i=0; i<4; i++)
            for(int j=0; j<4; j++)
                w[i][j] = (byte)(w1[i][j]^w2[i][j]);
        return w;
    }

    private static void copy_block(byte[][] estat, byte[] C, int i) {
        for(int j=0; j<4; j++)
            for(int k=0; k<4; k++)
                C[i+k+4*j] = estat[k][j];
    }

    private static byte[][] get_key(int i, byte[][][] W) {
        byte[][] key = new byte[4][4];
        for(int j=0; j<4; j++)
            for(int k=0; k<4; k++)
                key[k][j] = W[i][k][j];
        return key;
    }

    private static byte[][] get_block(byte[] M, int i) {
        byte[][] estat = new byte[4][4];
        for(int j=0; j<4; j++)
            for(int k=0; k<4; k++)
                estat[k][j] = M[i+k+4*j];
        return estat;
    }
    
    private static byte[][] expandKey(BigInteger K, int Nk, int Nr) {
        byte[][] W   = new byte[4][(Nr+1)*4];
        byte[] key   = new byte[4*Nk];
        byte[] bytes = K.toByteArray();
        int    diff  = 4*Nk-bytes.length;
        // toByteArray deletes initial zeros -> changes the key!!!
        for(int i=0; i<diff; i++) key[i] = 0;
        for(int i=diff; i<4*Nk; i++) key[i] = bytes[i-diff];
        // initial key
        for(int i=0; i<Nk; i++)
            for(int j=0; j<4; j++)
                W[j][i] = key[j+4*i];
        // key expansion
        byte[] temp = new byte[4];
        for(int i=Nk; i<4*(Nr+1); i++) {
            for(int k=0; k<4; k++) temp[k] = W[k][i-1];
            if(i%Nk==0) temp = xor(SubWord(RotWord(temp)),Rcon(i/Nk));
            else if(Nk>6 && i%Nk==4) temp = SubWord(temp);
            for(int k=0; k<4; k++) W[k][i] = (byte)(W[k][i-Nk]^temp[k]);
        }
        return W; 
    }
   
    // adds initial IV and pads original data as follows:
    // 1- add a single 1 bit
    // 2- add zeroes until 8 bytes are left (possibly no zeroes added)
    // 3- store original message length on the last 8 bytes
    // 4- add aditional full block (16 bytes) if needed for 1-3.
    private static byte[] IVpadMessage(byte[] M, byte[] IV) {
        // compute pad variable wich controls main if
        int pad, n = M.length;
        if(n%16 == 0)   pad=0; // add one block and pad it
        else if(n%16<8) pad=1; // pad existent block
        else            pad=2; // pad existent block and pad new block
        // allocate space for IV + padded plain text
        int size; 
        if(pad==0 || pad==1) size = ((n/16)+2)*16;
        else                 size = ((n/16)+3)*16;
        byte[] Mpad = new byte[size];
        // set IV as the first block
        for(int i=0; i<16; i++) Mpad[i] = IV[i];
        byte[]   m_length;
        // loop that copies blocks of data
        for(int i=0; i+16<=n; i+=16) copy_block(get_block(M,i),Mpad,i+16);
        // add new block and pad new block
        if(pad==0) {
            // add first byte 0x80
            Mpad[n+16]=(byte)0x80;
            // add 7 0x00 bytes
            for(int i=1; i<8; i++) Mpad[n+i+16]=0x00;
            // store message length in bits at the last 8 bytes
            m_length = ByteBuffer.allocate(8).putLong(n*8).array();
            for(int i=8,j=0; i<16; i++,j++) Mpad[n+i+16]=m_length[j];
        }
        // pad current block
        else if(pad==1) {
            // copy left bytes form M to C
            int pos=n-(16-(16-n%16));
            for(int i=pos; i<n; i++) Mpad[i+16] = M[i];
            // add first byte 0x80
            Mpad[n+16]=(byte)0x80;
            // add 0x00 bytes until there are 8 bytes left
            for(int i=n+1; i%16!=8; i++) Mpad[i+16]=0x00;
            // store message length in bits at the last 8 bytes
            m_length = ByteBuffer.allocate(8).putLong(n*8).array();
            for(int i=pos+8,j=0; j<8; i++,j++) Mpad[i+16]=m_length[j];
        }
        // pad current block, add new block, padd new block
        else if(pad==2) {
            /* FIRST BLOCK */
            // copy left bytes form M to C
            int pos=n-(16-(16-n%16));
            for(int i=pos; i<n; i++) Mpad[i+16] = M[i];
            // add first byte 0x80
            Mpad[n+16]=(byte)0x80;
            // add 0x00 bytes until the end of the block
            for(int i=n+1; i<pos+16; i++) Mpad[i+16]=0x00;
            /* SECOND BLOCK */
            pos+=16;
            for(int i=0; i<8; i++) Mpad[i+pos+16]=0x00;
            // store message length in bits at the last 8 bytes
            m_length = ByteBuffer.allocate(8).putLong(n*8).array();
            for(int i=pos+8,j=0; j<8; i++,j++) Mpad[i+16]=m_length[j];
        }
        return Mpad;
    }

    private static byte[][] copy_state(byte[][] state) {
        byte[][] res = new byte[4][4];
        for(int i=0; i<4; i++)
            for(int j=0; j<4; j++)
               res[j][i] = state[j][i];
        return res;
    }

    /* ************************ */
    /* PUBLIC AUXILIARY METHODS */
    /* ************************ */

    // These methods can be removed safetely.

    public static String getLogTables(int col) {
        StringBuilder out = new StringBuilder();
        out.append("Generator: 0x03\n");
        out.append("Log table:");
        for(int i=0;i<256;i++) {
            if(i%col==0) out.append("\n");
            out.append(String.format("%02x ",log[i]));
        }

        out.append("\n\nAnti-log table:");
        for(int i=0;i<256;i++) {
            if(i%col==0) out.append("\n");
            out.append(String.format("%02x ",alog[i]));
        }
        
        out.append("\n\nInverse table:");
        for(int i=0;i<256;i++) {
            if(i%col==0) out.append("\n");
            out.append(String.format("%02x ",inv[i]));
        }
        out.append("\n");
        return out.toString();
    }

    public static String getSboxTables(int col) {
        StringBuilder out = new StringBuilder();
        out.append("S-Box Table:");
        for(int i=0;i<256;i++) {
            if(i%col==0) out.append("\n");
            out.append(String.format("%02x ",sbox[i]));
        }

        out.append("\n\nInverse S-Box Table:");
        for(int i=0;i<256;i++) {
            if(i%col==0) out.append("\n");
            out.append(String.format("%02x ",invsb[i]));
        }
        return out.toString();
    }

    public static String stateToString(byte[][] estat) {   
        StringBuilder sb = new StringBuilder();
        for(int i=0; i<4; i++) {
            for(int j=0; j<4; j++)
                sb.append(String.format("%02x ",estat[i][j]));
            sb.append("\n");
        }
        return sb.toString();           
    }
    
    public static String keyToString(byte[][][] W, int Nr) {
        StringBuilder out = new StringBuilder();
        for(int i=0; i<Nr+1;i++) {
            for(int j=0; j<4; j++) 
                for(int k=0; k<4; k++)
                   out.append(String.format("%02x",W[i][k][j]));
            out.append("\n");
        }
        return out.toString();
    }

    public static String getMessage(byte[] M) {
        StringBuilder out = new StringBuilder();
        for(int i=0; i<M.length; i++) {
            if(i%16==0) out.append("\n");
            out.append(String.format("%02x",M[i]));
        }
        return out.toString();
    }
} // END_CLASS
