#![allow(dead_code, non_camel_case_types, non_snake_case, non_upper_case_globals, unused_variables)]
extern crate libc;

use libc::{toupper, tolower, strcmp, calloc, malloc, realloc, free, memset, memcpy, c_void};
use std::mem::size_of;
use std::process::exit;
use std::ptr::{null, null_mut};

const DF_SIZE_REAL: usize = 0x2000;
const CT_TYPE1_PID_CNT_MAX: usize = 32;
const CT1_TABLE_SIZE: usize = 256;
const CT2_TABLE_SIZE: usize = 0x1000;
const CT3_TABLE_SIZE: usize = 0x1000;
const CT4_TABLE_SIZE: usize = 0x20000;
const CT8_TABLE_SIZE: usize = 0x20000;
const RECURSIVE_CT_SIZE: usize = 4096;

const INIT_HASH_SIZE: usize = 65536;
const RECURSIVE_BOUNDARY: usize = 10;

static pattern_interval: usize = 0;
static min_pattern_interval: usize = 0;

static mut xlatcase: [i32; 256] = [0; 256];

static mut dfc_total_memory: usize = 0;
static mut dfc_pattern_memory: usize = 0;
static mut dfc_memory_dfs: usize = DF_SIZE_REAL * 14;
static mut dfc_memory_ct1: usize = 0;
static mut dfc_memory_ct2: usize = 0;
static mut dfc_memory_ct3: usize = 0;
static mut dfc_memory_ct4: usize = 0;
static mut dfc_memory_ct8: usize = 0;

type PID_TYPE = u32;
type PID_CNT_TYPE = u32;
type BUC_CNT_TYPE = u32;

type DTYPE = u16;
type BTYPE = u16;

macro_rules! BINDEX { ($x:expr) => ($x >> 3) }
macro_rules! BMASK { ($x:expr) => (1 << (($x) & 0x7)) }

struct DFC_STRUCTURE {
    init_hash: *mut *const DFC_PATTERN,
    dfcPatterns: *mut DFC_PATTERN,
    dfcMatchList: *const *const DFC_PATTERN,

    numPatterns: u32,

    /// Direct Filter (DF1) for all patterns
    DirectFilter1: [u8; DF_SIZE_REAL],

    cDF0: [u8; 256],
    cDF1: [u8; DF_SIZE_REAL],
    cDF2: [u8; DF_SIZE_REAL],

    ADD_DF_4_plus: [u8; DF_SIZE_REAL],
    ADD_DF_4_1: [u8; DF_SIZE_REAL],

    ADD_DF_8_1: [u8; DF_SIZE_REAL],
    ADD_DF_8_2: [u8; DF_SIZE_REAL],

    /* Compact Table (CT1) for 1B patterns */
    CompactTable1: [CT_Type_1; CT1_TABLE_SIZE],

    /* Compact Table (CT2) for 2B patterns */
    CompactTable2: [CT_Type_2; CT2_TABLE_SIZE],

    /* Compact Table (CT4) for 4B ~ 7B patterns */
    CompactTable4: [CT_Type_2; CT4_TABLE_SIZE],

    /* Compact Table (CT8) for 8B ~ patterns */
    CompactTable8: [CT_Type_2_8B; CT8_TABLE_SIZE],
}

struct DFC_PATTERN {
    next: *mut DFC_PATTERN,

    patrn: *mut u8, // upper case pattern
    casepatrn: *mut u8, // original pattern
    n: usize, // Patternlength
    nocase: bool, // Flag for case-sensitivity. (0: case-sensitive pattern, 1: opposite)

    sids_size: usize,
    sids: *mut PID_TYPE, // external id (unique)
    iid: PID_TYPE, // internal id (used in DFC library only)
}

#[derive(Clone, Copy)]
struct CT_Type_1 {
    pid: [PID_TYPE; CT_TYPE1_PID_CNT_MAX],
    cnt: u16,
}

#[derive(Clone, Copy)]
struct CT_Type_2 {
    cnt: BUC_CNT_TYPE,
    array: *const CT_Type_2_Array,
}

struct CT_Type_2_Array {
    pat: u32, // Maximum 4B pattern
    cnt: PID_CNT_TYPE, // Number of PIDs
    pid: *const PID_TYPE, // list of PIDs
    DirectFilter: *const u8,
    CompactTable: *const CT_Type_2_2B,
}

#[derive(Clone, Copy)]
struct CT_Type_2_8B {
    cnt: BUC_CNT_TYPE,
    array: *const CT_Type_2_8B_Array,
}

struct CT_Type_2_8B_Array {
    pat: u32, // 8B pattern
    cnt: PID_CNT_TYPE, // Number of PIDs
    pid: *const PID_TYPE, // list of PIDs
    DirectFilter: *const u8,
    CompactTable: *const CT_Type_2_2B,
}

struct CT_Type_2_2B_Array {
    pat: u16, // 2B pattern
    cnt: PID_CNT_TYPE, // Number of PIDs
    pid: *const PID_TYPE, // list of PIDs
}

struct CT_Type_2_2B {
    cnt: BUC_CNT_TYPE,
    array: *const CT_Type_2_2B_Array,
}

#[derive(Debug)]
enum dfcMemoryType {
    DFC_MEMORY_TYPE__NONE = 0,
    DFC_MEMORY_TYPE__DFC,
    DFC_MEMORY_TYPE__PATTERN,
    DFC_MEMORY_TYPE__CT1,
    DFC_MEMORY_TYPE__CT2,
    DFC_MEMORY_TYPE__CT3,
    DFC_MEMORY_TYPE__CT4,
    DFC_MEMORY_TYPE__CT8,
}

#[derive(Debug)]
enum dfcDataType {
    DFC_NONE = 0,
    DFC_PID_TYPE,
    DFC_CT_Type_2_Array,
    DFC_CT_Type_2_2B_Array,
    DFC_CT_Type_2_8B_Array,
}

unsafe fn DFC_New() -> *mut DFC_STRUCTURE {
    init_xlatcase();

    dfc_total_memory = 0;
    dfc_pattern_memory = 0;

    let p = DFC_MALLOC(size_of::<DFC_STRUCTURE>(),
                       dfcMemoryType::DFC_MEMORY_TYPE__DFC) as *mut DFC_STRUCTURE;

    if !p.is_null() {
        memset(p as *mut c_void, 0, size_of::<DFC_STRUCTURE>());
        (*p).init_hash = malloc(size_of::<*mut DFC_PATTERN>() * INIT_HASH_SIZE) as *mut *const DFC_PATTERN;
        if (*p).init_hash.is_null() {
            exit(1);
        }
        memset((*p).init_hash as *mut c_void,
               0,
               size_of::<*mut DFC_PATTERN>() * INIT_HASH_SIZE);
    }

    p
}

unsafe fn DFC_FreePattern(p: *mut DFC_PATTERN) {
    if !(*p).patrn.is_null() {
        free((*p).patrn as *mut c_void);
    }

    if !(*p).casepatrn.is_null() {
        free((*p).casepatrn as *mut c_void);
    }
}

unsafe fn DFC_FreePatternList(dfc: *mut DFC_STRUCTURE) {
    let mut plist = (*dfc).dfcPatterns;
    let mut p_next;

    while !plist.is_null() {
        DFC_FreePattern(plist);
        p_next = (*plist).next;
        free(plist as *mut c_void);
        plist = p_next;
    }
}

unsafe fn DFC_FreeStructure(dfc: *mut DFC_STRUCTURE) {
    if dfc.is_null() {
        return;
    }

    if !(*dfc).dfcPatterns.is_null() {
        DFC_FreePatternList(dfc);
    }

    if !(*dfc).dfcMatchList.is_null() {
        free((*dfc).dfcMatchList as *mut c_void);
    }

    for i in 0..CT2_TABLE_SIZE {
        for j in 0..(*dfc).CompactTable2[i].cnt {
            free((*(*dfc).CompactTable2[i].array.offset(j as isize)).pid as *mut c_void);

            if !(*(*dfc).CompactTable2[i].array.offset(j as isize)).DirectFilter.is_null() {
                free((*(*dfc).CompactTable2[i].array.offset(j as isize)).DirectFilter as *mut c_void);
            }

            if !(*(*dfc).CompactTable2[i].array.offset(j as isize)).CompactTable.is_null() {
                for k in 0..RECURSIVE_CT_SIZE {
                    for l in 0..
                             (*(*(*dfc).CompactTable2[i].array.offset(j as isize)).CompactTable.offset(k as isize))
                        .cnt {
                        free((*(*(*(*dfc).CompactTable2[i].array.offset(j as isize))
                                    .CompactTable
                                    .offset(k as isize))
                                .array
                                .offset(l as isize))
                            .pid as *mut c_void);
                    }
                    free((*(*(*dfc).CompactTable2[i].array.offset(j as isize)).CompactTable.offset(k as isize))
                        .array as *mut c_void);
                }
                free((*(*dfc).CompactTable2[i].array.offset(j as isize)).CompactTable as *mut c_void);
            }
        }
    }

    for i in 0..CT4_TABLE_SIZE {
        for j in 0..(*dfc).CompactTable4[i].cnt {
            free((*(*dfc).CompactTable4[i].array.offset(j as isize)).pid as *mut c_void);

            if !(*(*dfc).CompactTable4[i].array.offset(j as isize)).DirectFilter.is_null() {
                free((*(*dfc).CompactTable4[i].array.offset(j as isize)).DirectFilter as *mut c_void);
            }

            if !(*(*dfc).CompactTable4[i].array.offset(j as isize)).CompactTable.is_null() {
                for k in 0..RECURSIVE_CT_SIZE {
                    for l in 0..
                             (*(*(*dfc).CompactTable4[i].array.offset(j as isize)).CompactTable.offset(k as isize))
                        .cnt {
                        free((*(*(*(*dfc).CompactTable4[i].array.offset(j as isize))
                                    .CompactTable
                                    .offset(k as isize))
                                .array
                                .offset(l as isize))
                            .pid as *mut c_void);
                    }
                    free((*(*(*dfc).CompactTable4[i].array.offset(j as isize)).CompactTable.offset(k as isize))
                        .array as *mut c_void);
                }
                free((*(*dfc).CompactTable4[i].array.offset(j as isize)).CompactTable as *mut c_void);
            }
        }
    }

    for i in 0..CT8_TABLE_SIZE {
        for j in 0..(*dfc).CompactTable8[i].cnt {
            free((*(*dfc).CompactTable8[i].array.offset(j as isize)).pid as *mut c_void);

            if !(*(*dfc).CompactTable8[i].array.offset(j as isize)).DirectFilter.is_null() {
                free((*(*dfc).CompactTable8[i].array.offset(j as isize)).DirectFilter as *mut c_void);
            }

            if !(*(*dfc).CompactTable8[i].array.offset(j as isize)).CompactTable.is_null() {
                for k in 0..RECURSIVE_CT_SIZE {
                    for l in 0..
                             (*(*(*dfc).CompactTable8[i].array.offset(j as isize)).CompactTable.offset(k as isize))
                        .cnt {
                        free((*(*(*(*dfc).CompactTable8[i].array.offset(j as isize))
                                    .CompactTable
                                    .offset(k as isize))
                                .array
                                .offset(l as isize))
                            .pid as *mut c_void);
                    }
                    free((*(*(*dfc).CompactTable8[i].array.offset(j as isize)).CompactTable.offset(k as isize))
                        .array as *mut c_void);
                }
                free((*(*dfc).CompactTable8[i].array.offset(j as isize)).CompactTable as *mut c_void);
            }
        }
    }

    free(dfc as *mut c_void);
}

unsafe fn DFC_AddPattern(dfc: *mut DFC_STRUCTURE, pat: *const u8, n: usize, nocase: bool, sid: PID_TYPE) -> i32 {
    let mut plist = DFC_InitHashLookup(dfc, pat, n);

    if plist.is_null() {
        plist = DFC_MALLOC(size_of::<DFC_PATTERN>(),
                           dfcMemoryType::DFC_MEMORY_TYPE__PATTERN) as *mut DFC_PATTERN;
        memset(plist as *mut c_void, 0, size_of::<DFC_PATTERN>());

        (*plist).patrn = DFC_MALLOC(n, dfcMemoryType::DFC_MEMORY_TYPE__PATTERN) as *mut u8;

        ConvertCaseEx((*plist).patrn, pat, n);

        (*plist).casepatrn = DFC_MALLOC(n, dfcMemoryType::DFC_MEMORY_TYPE__PATTERN) as *mut u8;

        memcpy((*plist).casepatrn as *mut c_void, pat as *const c_void, n);

        (*plist).n = n;
        (*plist).nocase = nocase;
        (*plist).iid = (*dfc).numPatterns; // internal id
        (*plist).next = null_mut();

        DFC_InitHashAdd(dfc, plist);

        // sid update
        (*plist).sids_size = 1;
        (*plist).sids = DFC_MALLOC(size_of::<PID_TYPE>(),
                                   dfcMemoryType::DFC_MEMORY_TYPE__PATTERN) as *mut PID_TYPE;
        *(*plist).sids.offset(0) = sid;

        // Add this pattern to the list
        (*dfc).numPatterns += 1;

        0
    } else {
        let mut found = false;

        for x in 0..(*plist).sids_size {
            if *(*plist).sids.offset(x as isize) == sid {
                found = true;
                break;
            }
        }

        if !found {
            let sids = DFC_REALLOC((*plist).sids as *mut c_void,
                                   (*plist).sids_size + 1,
                                   dfcDataType::DFC_PID_TYPE,
                                   dfcMemoryType::DFC_MEMORY_TYPE__PATTERN) as *mut u32;
            (*plist).sids = sids;
            *(*plist).sids.offset((*plist).sids_size as isize) = sid;
            (*plist).sids_size += 1;
        }

        1
    }
}

unsafe fn DFC_PrintInfo(dfc: *mut DFC_STRUCTURE) {
    unimplemented!()
}

unsafe fn Add_PID_to_2B_CT(CompactTable: *const CT_Type_2_2B,
                           temp: *mut u8,
                           pid: PID_TYPE,
                           memory_type: dfcMemoryType) {
    unimplemented!()
}

unsafe fn DFC_Compile(dfc: *mut DFC_STRUCTURE) -> i32 {
    unimplemented!()
}

unsafe fn Verification_CT1(dfc: *const DFC_STRUCTURE,
                           buf: *const u8,
                           matches: u32,
                           match_fn: fn(*const u8, *const u32, usize),
                           starting_point: *const u8)
                           -> u32 {

    unimplemented!()
}

unsafe fn Verification_CT2(dfc: *const DFC_STRUCTURE,
                           buf: *const u8,
                           matches: u32,
                           match_fn: fn(*const u8, *const u32, usize),
                           starting_point: *const u8)
                           -> u32 {
    unimplemented!()
}

unsafe fn Verification_CT4_7(dfc: *const DFC_STRUCTURE,
                             buf: *const u8,
                             matches: u32,
                             match_fn: fn(*const u8, *const u32, usize),
                             starting_point: *const u8)
                             -> u32 {
    unimplemented!()
}

unsafe fn Verification_CT8_plus(dfc: *const DFC_STRUCTURE,
                                buf: *const u8,
                                matches: u32,
                                match_fn: fn(*const u8, *const u32, usize),
                                starting_point: *const u8)
                                -> u32 {
    unimplemented!()
}

unsafe fn Progressive_Filtering(dfc: *const DFC_STRUCTURE,
                                buf: *const u8,
                                mut matches: u32,
                                idx: BTYPE,
                                msk: BTYPE,
                                match_fn: fn(*const u8, *const u32, usize),
                                starting_point: *const u8,
                                rest_len: usize)
                                -> u32 {

    if (*dfc).cDF0[*buf.offset(-2) as usize] != 0 {
        matches = Verification_CT1(dfc, buf, matches, match_fn, starting_point);
    }

    if (*dfc).cDF1[idx as usize] & msk as u8 != 0 {
        matches = Verification_CT2(dfc, buf, matches, match_fn, starting_point);
    }

    if rest_len >= 4 {
        let data = *(buf) as u16;
        let index = BINDEX!(data);
        let mask = BMASK!(data);

        if mask & (*dfc).ADD_DF_4_plus[index as usize] != 0 {
            if mask & (*dfc).ADD_DF_4_1[index as usize] != 0 {
                matches = Verification_CT4_7(dfc, buf, matches, match_fn, starting_point);
            }

            if rest_len >= 8 {
                matches = Verification_CT8_plus(dfc, buf, matches, match_fn, starting_point);
            }
        }
    }

    matches
}

unsafe fn DFC_Search(dfc: *const DFC_STRUCTURE,
                     buf: *const u8,
                     buflen: usize,
                     match_fn: fn(*const u8, *const u32, usize))
                     -> u32 {
    let mut matches = 0;

    if buflen <= 0 {
        return 0;
    }

    let DirectFilter1 = (*dfc).DirectFilter1;

    for i in 0..buflen - 1 {
        let data = *(buf.offset(i as isize)) as u16;
        let index = BINDEX!(data);
        let mask = BMASK!(data);

        if DirectFilter1[index as usize] & mask as u8 != 0 {
            matches = Progressive_Filtering(dfc,
                                            buf.offset(i as isize + 2),
                                            matches,
                                            index,
                                            mask,
                                            match_fn,
                                            buf,
                                            buflen - i);
        }
    }

    // It is needed to check last 1 byte from payload
    if (*dfc).cDF0[*buf.offset(buflen as isize - 1) as usize] != 0 {
        for i in 0..(*dfc).CompactTable1[*buf.offset(buflen as isize - 1) as usize].cnt {
            let pid = (*dfc).CompactTable1[*buf.offset(buflen as isize - 1) as usize].pid[i as usize];
            let mlist = *(*dfc).dfcMatchList.offset(pid as isize);

            match_fn((*mlist).casepatrn, (*mlist).sids, (*mlist).sids_size);
            matches += 1;
        }
    }

    matches
}

fn my_sqrtf(input: f32, mut x: f32) -> f32 {
    if x == 0f32 && input == 0f32 {
        return 0f32;
    }

    for i in 0..10 {
        x = (x + (input / x)) / 2f32;
    }
    x
}

unsafe fn init_xlatcase() {
    for i in 0..257 {
        xlatcase[i] = toupper(i as i32);
    }
}

unsafe fn ConvertCaseEx(d: *mut u8, s: *const u8, m: usize) {
    for i in 0..m {
        *d.offset(i as isize) = xlatcase[s.offset(i as isize) as usize] as u8;
    }
}

unsafe fn my_strncmp(a: *const u8, b: *const u8, n: i32) -> i32 {
    for i in 0..n {
        if *a.offset(i as isize) != *b.offset(i as isize) {
            return -1;
        }
    }
    0
}

unsafe fn my_strncasecmp(a: *const u8, b: *const u8, n: i32) -> i32 {
    for i in 0..n {
        if tolower(*a.offset(i as isize) as i32) != tolower(*b.offset(i as isize) as i32) {
            return -1;
        }
    }
    0
}

unsafe fn DFC_REALLOC(mut p: *mut c_void,
                      n: usize,
                      data_type: dfcDataType,
                      memory_type: dfcMemoryType)
                      -> *const c_void {
    match data_type {
        dfcDataType::DFC_PID_TYPE => {
            p = realloc(p, size_of::<PID_TYPE>() * n);
            dfc_total_memory += size_of::<PID_TYPE>();
            match memory_type {
                dfcMemoryType::DFC_MEMORY_TYPE__PATTERN => dfc_pattern_memory += size_of::<PID_TYPE>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT2 => dfc_memory_ct2 += size_of::<PID_TYPE>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT3 => dfc_memory_ct3 += size_of::<PID_TYPE>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT4 => dfc_memory_ct4 += size_of::<PID_TYPE>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT8 => dfc_memory_ct8 += size_of::<PID_TYPE>(),
                _ => {}
            }
            return p;
        }
        dfcDataType::DFC_CT_Type_2_Array => {
            p = realloc(p, size_of::<CT_Type_2_Array>() * n);
            dfc_total_memory += size_of::<CT_Type_2_Array>();
            match memory_type {
                dfcMemoryType::DFC_MEMORY_TYPE__CT2 => dfc_memory_ct2 += size_of::<CT_Type_2_Array>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT3 => dfc_memory_ct3 += size_of::<CT_Type_2_Array>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT4 => dfc_memory_ct4 += size_of::<CT_Type_2_Array>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT8 => dfc_memory_ct8 += size_of::<CT_Type_2_Array>(),
                _ => {}
            }
            return p;
        }
        dfcDataType::DFC_CT_Type_2_2B_Array => {
            p = realloc(p, size_of::<CT_Type_2_2B_Array>() * n);
            dfc_total_memory += size_of::<CT_Type_2_2B_Array>();
            match memory_type {
                dfcMemoryType::DFC_MEMORY_TYPE__CT2 => dfc_memory_ct2 += size_of::<CT_Type_2_2B_Array>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT3 => dfc_memory_ct3 += size_of::<CT_Type_2_2B_Array>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT4 => dfc_memory_ct4 += size_of::<CT_Type_2_2B_Array>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT8 => dfc_memory_ct8 += size_of::<CT_Type_2_2B_Array>(),
                _ => {}
            }
            return p;
        }
        dfcDataType::DFC_CT_Type_2_8B_Array => {
            p = realloc(p, size_of::<CT_Type_2_8B_Array>() * n);
            dfc_total_memory += size_of::<CT_Type_2_8B_Array>();
            match memory_type {
                dfcMemoryType::DFC_MEMORY_TYPE__CT2 => dfc_memory_ct2 += size_of::<CT_Type_2_8B_Array>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT3 => dfc_memory_ct3 += size_of::<CT_Type_2_8B_Array>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT4 => dfc_memory_ct4 += size_of::<CT_Type_2_8B_Array>(),
                dfcMemoryType::DFC_MEMORY_TYPE__CT8 => dfc_memory_ct8 += size_of::<CT_Type_2_8B_Array>(),
                _ => {}
            }
            return p;
        }
        _ => {
            println!("ERROR! Data Type is not correct!");
        }
    }
    null()
}

unsafe fn DFC_FREE(p: *mut c_void, n: usize, memory_type: dfcMemoryType) {
    free(p);
    match memory_type {
        dfcMemoryType::DFC_MEMORY_TYPE__DFC => {}
        dfcMemoryType::DFC_MEMORY_TYPE__PATTERN => {
            dfc_pattern_memory -= n;
            dfc_memory_ct2 -= n;
        }
        dfcMemoryType::DFC_MEMORY_TYPE__CT3 => dfc_memory_ct3 -= n,
        dfcMemoryType::DFC_MEMORY_TYPE__CT4 => dfc_memory_ct4 -= n,
        dfcMemoryType::DFC_MEMORY_TYPE__CT8 => dfc_memory_ct8 -= n,
        dfcMemoryType::DFC_MEMORY_TYPE__NONE => {}
        _ => println!("Invalid memory type: {:?}", memory_type),
    }
    dfc_total_memory -= n;
}

unsafe fn DFC_MALLOC(n: usize, memory_type: dfcMemoryType) -> *const c_void {
    let p = calloc(1, n); // initialize it to 0

    if !p.is_null() {
        match memory_type {
            dfcMemoryType::DFC_MEMORY_TYPE__DFC => {}
            dfcMemoryType::DFC_MEMORY_TYPE__PATTERN => dfc_pattern_memory += n,
            dfcMemoryType::DFC_MEMORY_TYPE__CT2 => dfc_memory_ct2 += n,
            dfcMemoryType::DFC_MEMORY_TYPE__CT3 => dfc_memory_ct3 += n,
            dfcMemoryType::DFC_MEMORY_TYPE__CT4 => dfc_memory_ct4 += n,
            dfcMemoryType::DFC_MEMORY_TYPE__CT8 => dfc_memory_ct8 += n,
            dfcMemoryType::DFC_MEMORY_TYPE__NONE => {}
            _ => {
                println!("Invalid memory type: {:?}", memory_type);
            }
        };
        dfc_total_memory += n;
    }
    p
}

unsafe fn Build_pattern(p: *const DFC_PATTERN, flag: *const u8, temp: *mut u8, i: u32, j: isize, k: isize) {
    if !(*p).nocase {
        if (*(*p).patrn.offset(j) >= 65 && *(*p).patrn.offset(j) <= 90) ||
           (*(*p).patrn.offset(j) >= 97 && *(*p).patrn.offset(j) <= 122) {
            if *flag.offset(k) == 0 {
                *temp.offset(k) = tolower(*(*p).patrn.offset(j) as i32) as u8;
            } else {
                *temp.offset(k) = toupper(*(*p).patrn.offset(j) as i32) as u8;
            }
        } else {
            *temp.offset(k) = *(*p).patrn.offset(j);
        }
    } else {
        *temp.offset(k) = *(*p).casepatrn.offset(j); // original pattern
    }
    return;
}

unsafe fn DFC_InitHashRaw(pat: *const u8, patlen: usize) -> u32 {
    let mut hash = patlen as u32 * *pat.offset(0) as u32;
    if patlen > 1 {
        hash += *pat.offset(1) as u32;
    }
    hash % INIT_HASH_SIZE as u32
}

unsafe fn DFC_InitHashLookup(ctx: *const DFC_STRUCTURE, pat: *const u8, patlen: usize) -> *mut DFC_PATTERN {
    let hash = DFC_InitHashRaw(pat, patlen);

    if (*ctx).init_hash.is_null() {
        return null_mut();
    }

    let mut t = *(*ctx).init_hash.offset(hash as isize);

    while !t.is_null() {
        if strcmp((*t).casepatrn as *const i8, pat as *const i8) != 0 {
            return t as *mut DFC_PATTERN;
        }
        t = (*t).next;
    }

    null_mut()
}

unsafe fn DFC_InitHashAdd(ctx: *const DFC_STRUCTURE, p: *mut DFC_PATTERN) -> i32 {
    let hash = DFC_InitHashRaw((*p).casepatrn, (*p).n);

    if (*ctx).init_hash.is_null() {
        return 0;
    }

    if (*ctx).init_hash.offset(hash as isize).is_null() {
        *(*ctx).init_hash.offset(hash as isize) = p;
        return 0;
    }

    let mut tt = null_mut();
    let mut t = *(*ctx).init_hash.offset(hash as isize) as *mut DFC_PATTERN;

    // get the list tail
    while !t.is_null() {
        tt = t;
        t = (*t).next;
    }

    (*tt).next = p;

    0
}
