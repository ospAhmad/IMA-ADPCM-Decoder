/*
ADPCM Decoder/Encoder program written in pure pure rust.
the implementation of this code is followed as columbia univ's ADPCM implementation paper.

-paper of the pdf file can be found here-
http://www.cs.columbia.edu/~hgs/audio/dvi/IMA_ADPCM.pdf
http://www.cs.columbia.edu/~sedwards/classes/2004/4840/reports/manic.pdf
 */
use byteorder::{ByteOrder, LittleEndian};
use std::collections::btree_set::Difference;
use std::convert::TryInto;
use std::fs::{File,OpenOptions};
use std::hash::Hash;
use std::io::{prelude::*, IoSlice};
use std::path::Path;
use std::collections::HashMap;
use std::str::Bytes;
use std::sync::Arc;

// 44bytes
const LENGTH_TABLE: [u8;13] = [
    // RIFF Chunk
    4,4,4,
    // fmt sub chunk
    4,4,2,2,4,4,2,2,
    //data sub chunk
    4,4
];

const DESCRIPTION_TABLE: [&str;13]=[
    "Chunk_id: marks the file as a riff file.",
    "Chunk_data_size: size of the overall file.",
    "Riff_type_id: file type header, maybe will be wave.",
    "Chunk1. maybe fmt.",
    "Chunk 1 size",
    "Format. 1 is for PCM.",
    "Channels",
    "sample_rate",
    "byte_rate",
    "block_align",
    "Bits per sample ",
    "Data chunk header",
    "Data size",
];

const STEPSIZE_TABLE: [i32; 89]=[
    7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 
    19, 21, 23, 25, 28, 31, 34, 37, 41, 45, 
    50, 55, 60, 66, 73, 80, 88, 97, 107, 118, 
    130, 143, 157, 173, 190, 209, 230, 253, 279, 307,
    337, 371, 408, 449, 494, 544, 598, 658, 724, 796,
    876, 963, 1060, 1166, 1282, 1411, 1552, 1707, 1878, 2066, 
    2272, 2499, 2749, 3024, 3327, 3660, 4026, 4428, 4871, 5358,
    5894, 6484, 7132, 7845, 8630, 9493, 10442, 11487, 12635, 13899, 
    15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794, 32767 
    ];

const INDEX_TABLE: [i8;16]=[-1,-1,-1,-1, 2, 4, 6, 8,
                            -1,-1,-1,-1, 2, 4, 6, 8];
const LOOKUP_TABLE_1:  [i8;8]=[8,6,4,2,-1,-1,-1,-1];
const LOOKUP_TABLE_2: [i16;49]=[
                    16,17,19,21,23,25,28,31,34,37,41,45,
                    50,55,60,66,73,80,88,97,107,118,130,143,157,173,190,209,230,253,279,307,337,371,408,449,
                    494,544,598,658,724,796,876,963,1060,1160,1282,1411,
                    1552];
struct Wave {
    
    // actual ADPCM wav
    audio: Vec<u8>,
    current: usize,
    nibbles: Vec<u8>,
    /*
    // RIFF Chunk
    chunk_id: u8,
    chunk_data_size: u32,
    riff_type_id: u8,
    // format sub chunk
    chunk1_id: u8,// fmt
    chunk1_data_size: u32,// Size of the format chunk
    format_tag: u16,    //  format_Tag 1=PCM
    num_channels: u16,  //  1=Mono 2=Sterio
    sample_rate: u32,// Sampling Frequency in (44100)Hz
    byte_rate: u32,// Byte rate
    block_align:u16,     // 4
    bits_per_sample:u16,  // 16
    chunk2_id: u8, // data
    chunk2_data_size:u32,  // Size of the audio data    
     */
}
fn _nibblegen(tag:&u8)->[u8;2]{
    let rag = tag >> 4;
    let ag = rag<<4 ^tag;
    return [rag,ag];
}
impl Wave {

    fn new(filepath: &Path) -> Self {
        let mut file = File::open(filepath).unwrap();
        let  mut audio_buffer: Vec<u8> = Vec::new();
        file.read_to_end(&mut  audio_buffer).unwrap();
        let mut nibbles:Vec<u8> =  Vec::new();
        for x in  &audio_buffer[45..]{
            for z  in _nibblegen(&x){
                nibbles.push(z);
            }
        }
        Self {
            audio:audio_buffer,
            current: 0 as usize,
            nibbles
        }
    }
    fn seek(&mut self,length: usize) -> &[u8]{
        let target: &[u8] = &self.audio[self.current..self.current+length];
        self.current = &self.current+length;
        return target;
    }

    fn current(&self)->usize{
        return self.current.clone();
    }
    fn mv(&mut self, position: usize) {
        self.current = position;
    }
    fn dump_adpcm(&self,from: usize){
        let mut dump = File::create("dumped.adpcm").unwrap();
        dump.write_all(&self.audio[from..]).unwrap();
    }
    fn decode(&self){
        let mut index: i8=0;
        let mut stepsize:i32=7;
        //let  mut predicted=0;
        let mut diff:i32 =0;
        let mut new_sample: i32=0;
        let mut result: Vec<i16> = Vec::new();
        let mut count: u64 = 0;
        let mut new_sample_pushed:i16;
        let mut sample_as_usize: usize;
        let mut index_as_usize: usize;
        let mut sample:&u8;
        let mut previous = 0;
        /*
        sample: contains sample value, which is 4 bit ADPCM nibble.
        new_sample: contains 16 bit PCM data already compressed.
        diff: difference
        result: stores decompressed 16 bit pcm, in this case, it's new_sample will be pushed.
        index: current index of stepsize.
        stepsize: stepsize.
        
        */

        for current in 0..self.nibbles.len()-1{
            // sample contains 4 bit nibble, as u8.
            sample = &self.nibbles[current];
            diff=0;
            if sample&4 > 0{ 
                diff+=stepsize;
            }
            if sample&2 > 0{
                diff+=(stepsize>>1);
            }
            if sample&1 > 0{
                diff+=(stepsize >> 2);
            }
            diff+=(stepsize >> 3);
            if sample&8 > 0{
                diff=-diff;
            }
            
            new_sample = previous + diff;

            if new_sample > 32767{
                new_sample=32767;

            }
            else if new_sample < -32768{
                new_sample= -32768;
            }
            
            new_sample_pushed = new_sample as i16;
            result.push(new_sample_pushed);
            //println!("index: {}, index {}",*sample, *sample as usize);
            sample_as_usize=*sample as usize;
            index+=INDEX_TABLE[sample_as_usize];
            if index < 0{
                index=0
            }
            else if index > 88{
                index=88
            }

            index_as_usize=index as usize;
            stepsize=STEPSIZE_TABLE[index_as_usize];
            //println!("Index: {}, usize: {}",index,index_as_usize);
            
            previous = new_sample;
            
            count+=1;
        
        }
        let mut fb = File::create("out.pcm").unwrap();
        let mut ures: Vec<u8> = Vec::new();
        for i in result{
            for z in i.to_le_bytes().iter(){
                ures.push(*z);
            };
        }
        println!("Wirting to file...");
        fb.write_all(&ures).unwrap();
    }

}

fn main() {
    println!("building file information...");
    let mut wave:Wave = Wave::new(Path::new("target.wav"));
    let mut count = 0;
    for i in LENGTH_TABLE.iter().enumerate(){
        let data = wave.seek(*i.1 as usize);
        println!("{}: {:x?},",DESCRIPTION_TABLE[i.0],&data);
        count=count+i.0;
    }
    //println!("decoding adpcm samples...");
    //wave.decode();
    println!("dumping adpcm data...");
    wave.dump_adpcm(count);
}
