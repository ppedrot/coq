(***********************************************************************)
(*                                                                     *)
(*                         The CamlZip library                         *)
(*                                                                     *)
(*            Xavier Leroy, projet Cristal, INRIA Rocquencourt         *)
(*                                                                     *)
(*  Copyright 2001 Institut National de Recherche en Informatique et   *)
(*  en Automatique.  All rights reserved.  This file is distributed    *)
(*  under the terms of the GNU Lesser General Public License, with     *)
(*  the special exception on linking described in file LICENSE.        *)
(*                                                                     *)
(***********************************************************************)

(* $Id$ *)

(* Module [Zip]: reading and writing ZIP archives *)

(* crc32_table_b *)
let crc_table = [|
  0x00000000l; 0x77073096l; 0xEE0E612Cl; 0x990951BAl; 0x076DC419l; 0x706AF48Fl;
  0xE963A535l; 0x9E6495A3l; 0x0EDB8832l; 0x79DCB8A4l; 0xE0D5E91El; 0x97D2D988l;
  0x09B64C2Bl; 0x7EB17CBDl; 0xE7B82D07l; 0x90BF1D91l; 0x1DB71064l; 0x6AB020F2l;
  0xF3B97148l; 0x84BE41DEl; 0x1ADAD47Dl; 0x6DDDE4EBl; 0xF4D4B551l; 0x83D385C7l;
  0x136C9856l; 0x646BA8C0l; 0xFD62F97Al; 0x8A65C9ECl; 0x14015C4Fl; 0x63066CD9l;
  0xFA0F3D63l; 0x8D080DF5l; 0x3B6E20C8l; 0x4C69105El; 0xD56041E4l; 0xA2677172l;
  0x3C03E4D1l; 0x4B04D447l; 0xD20D85FDl; 0xA50AB56Bl; 0x35B5A8FAl; 0x42B2986Cl;
  0xDBBBC9D6l; 0xACBCF940l; 0x32D86CE3l; 0x45DF5C75l; 0xDCD60DCFl; 0xABD13D59l;
  0x26D930ACl; 0x51DE003Al; 0xC8D75180l; 0xBFD06116l; 0x21B4F4B5l; 0x56B3C423l;
  0xCFBA9599l; 0xB8BDA50Fl; 0x2802B89El; 0x5F058808l; 0xC60CD9B2l; 0xB10BE924l;
  0x2F6F7C87l; 0x58684C11l; 0xC1611DABl; 0xB6662D3Dl; 0x76DC4190l; 0x01DB7106l;
  0x98D220BCl; 0xEFD5102Al; 0x71B18589l; 0x06B6B51Fl; 0x9FBFE4A5l; 0xE8B8D433l;
  0x7807C9A2l; 0x0F00F934l; 0x9609A88El; 0xE10E9818l; 0x7F6A0DBBl; 0x086D3D2Dl;
  0x91646C97l; 0xE6635C01l; 0x6B6B51F4l; 0x1C6C6162l; 0x856530D8l; 0xF262004El;
  0x6C0695EDl; 0x1B01A57Bl; 0x8208F4C1l; 0xF50FC457l; 0x65B0D9C6l; 0x12B7E950l;
  0x8BBEB8EAl; 0xFCB9887Cl; 0x62DD1DDFl; 0x15DA2D49l; 0x8CD37CF3l; 0xFBD44C65l;
  0x4DB26158l; 0x3AB551CEl; 0xA3BC0074l; 0xD4BB30E2l; 0x4ADFA541l; 0x3DD895D7l;
  0xA4D1C46Dl; 0xD3D6F4FBl; 0x4369E96Al; 0x346ED9FCl; 0xAD678846l; 0xDA60B8D0l;
  0x44042D73l; 0x33031DE5l; 0xAA0A4C5Fl; 0xDD0D7CC9l; 0x5005713Cl; 0x270241AAl;
  0xBE0B1010l; 0xC90C2086l; 0x5768B525l; 0x206F85B3l; 0xB966D409l; 0xCE61E49Fl;
  0x5EDEF90El; 0x29D9C998l; 0xB0D09822l; 0xC7D7A8B4l; 0x59B33D17l; 0x2EB40D81l;
  0xB7BD5C3Bl; 0xC0BA6CADl; 0xEDB88320l; 0x9ABFB3B6l; 0x03B6E20Cl; 0x74B1D29Al;
  0xEAD54739l; 0x9DD277AFl; 0x04DB2615l; 0x73DC1683l; 0xE3630B12l; 0x94643B84l;
  0x0D6D6A3El; 0x7A6A5AA8l; 0xE40ECF0Bl; 0x9309FF9Dl; 0x0A00AE27l; 0x7D079EB1l;
  0xF00F9344l; 0x8708A3D2l; 0x1E01F268l; 0x6906C2FEl; 0xF762575Dl; 0x806567CBl;
  0x196C3671l; 0x6E6B06E7l; 0xFED41B76l; 0x89D32BE0l; 0x10DA7A5Al; 0x67DD4ACCl;
  0xF9B9DF6Fl; 0x8EBEEFF9l; 0x17B7BE43l; 0x60B08ED5l; 0xD6D6A3E8l; 0xA1D1937El;
  0x38D8C2C4l; 0x4FDFF252l; 0xD1BB67F1l; 0xA6BC5767l; 0x3FB506DDl; 0x48B2364Bl;
  0xD80D2BDAl; 0xAF0A1B4Cl; 0x36034AF6l; 0x41047A60l; 0xDF60EFC3l; 0xA867DF55l;
  0x316E8EEFl; 0x4669BE79l; 0xCB61B38Cl; 0xBC66831Al; 0x256FD2A0l; 0x5268E236l;
  0xCC0C7795l; 0xBB0B4703l; 0x220216B9l; 0x5505262Fl; 0xC5BA3BBEl; 0xB2BD0B28l;
  0x2BB45A92l; 0x5CB36A04l; 0xC2D7FFA7l; 0xB5D0CF31l; 0x2CD99E8Bl; 0x5BDEAE1Dl;
  0x9B64C2B0l; 0xEC63F226l; 0x756AA39Cl; 0x026D930Al; 0x9C0906A9l; 0xEB0E363Fl;
  0x72076785l; 0x05005713l; 0x95BF4A82l; 0xE2B87A14l; 0x7BB12BAEl; 0x0CB61B38l;
  0x92D28E9Bl; 0xE5D5BE0Dl; 0x7CDCEFB7l; 0x0BDBDF21l; 0x86D3D2D4l; 0xF1D4E242l;
  0x68DDB3F8l; 0x1FDA836El; 0x81BE16CDl; 0xF6B9265Bl; 0x6FB077E1l; 0x18B74777l;
  0x88085AE6l; 0xFF0F6A70l; 0x66063BCAl; 0x11010B5Cl; 0x8F659EFFl; 0xF862AE69l;
  0x616BFFD3l; 0x166CCF45l; 0xA00AE278l; 0xD70DD2EEl; 0x4E048354l; 0x3903B3C2l;
  0xA7672661l; 0xD06016F7l; 0x4969474Dl; 0x3E6E77DBl; 0xAED16A4Al; 0xD9D65ADCl;
  0x40DF0B66l; 0x37D83BF0l; 0xA9BCAE53l; 0xDEBB9EC5l; 0x47B2CF7Fl; 0x30B5FFE9l;
  0xBDBDF21Cl; 0xCABAC28Al; 0x53B39330l; 0x24B4A3A6l; 0xBAD03605l; 0xCDD70693l;
  0x54DE5729l; 0x23D967BFl; 0xB3667A2El; 0xC4614AB8l; 0x5D681B02l; 0x2A6F2B94l;
  0xB40BBE37l; 0xC30C8EA1l; 0x5A05DF1Bl; 0x2D02EF8Dl;
|]

let rec update_crc0 crc buf off len =
  let open Int32 in
  if Int.equal len 0 then crc
  else
    let i = (to_int (logand crc 0xFFl)) lxor (Char.code buf.[off]) in
    let crc = logxor (shift_right_logical crc 8) (Array.unsafe_get crc_table i) in
    update_crc0 crc buf (off + 1) (len - 1)

let update_crc_string crc buf off len =
  Int32.lognot @@ (update_crc0 (Int32.lognot crc) buf off len)

let update_crc crc buf off len =
  update_crc_string crc (Bytes.unsafe_to_string buf) off len

exception Error of string * string * string

let read1 = input_byte
let read2 ic =
  let lb = read1 ic in let hb = read1 ic in lb lor (hb lsl 8)
let read4 ic =
  let lw = read2 ic in let hw = read2 ic in
  Int32.logor (Int32.of_int lw) (Int32.shift_left (Int32.of_int hw) 16)
let read4_int ic =
  let lw = read2 ic in let hw = read2 ic in
  if hw > max_int lsr 16 then raise (Error("", "", "32-bit data too large"));
  lw lor (hw lsl 16)
let readstring ic n =
  let s = Bytes.create n in
  really_input ic s 0 n; Bytes.unsafe_to_string s

let write1 = output_byte
let write2 oc n =
  write1 oc n; write1 oc (n lsr 8)
let write4 oc n =
  write2 oc (Int32.to_int n);
  write2 oc (Int32.to_int (Int32.shift_right_logical n 16))
let write4_int oc n =
  write2 oc n;
  write2 oc (n lsr 16)
let writestring oc s =
  output_string oc s

type entry =
  { filename: string;
    extra: string;
    comment: string;
    mtime: float;
    crc: int32;
    uncompressed_size: int;
    compressed_size: int;
    is_directory: bool;
    file_offset: int64 }

type in_file =
  { if_filename: string;
    if_channel: Pervasives.in_channel;
    if_entries: entry list;
    if_directory: (string, entry) Hashtbl.t;
    if_comment: string }

let entries ifile = ifile.if_entries
let comment ifile = ifile.if_comment

type out_file =
  { of_filename: string;
    of_channel: Pervasives.out_channel;
    mutable of_entries: entry list;
    of_comment: string }

(* Return the position of the last occurrence of [pattern] in [buf],
   or -1 if not found. *)

let strrstr (pattern: string) (buf: bytes) ofs len =
  let rec search i j =
    if i < ofs then -1
    else if j >= String.length pattern then i
    else if String.get pattern j = Bytes.get buf (i + j) then search i (j+1)
    else search (i-1) 0
  in search (ofs + len - String.length pattern) 0

(* Determine if a file name is a directory (ends with /) *)

let filename_is_directory name =
  String.length name > 0 && name.[String.length name - 1] = '/'

(* Convert between Unix dates and DOS dates *)

let unixtime_of_dostime time date =
  fst(Unix.mktime
        { Unix.tm_sec = (time lsl 1) land 0x3e;
          Unix.tm_min = (time lsr 5) land 0x3f;
          Unix.tm_hour = (time lsr 11) land 0x1f;
          Unix.tm_mday = date land 0x1f;
          Unix.tm_mon = ((date lsr 5) land 0xf) - 1;
          Unix.tm_year = ((date lsr 9) land 0x7f) + 80;
          Unix.tm_wday = 0;
          Unix.tm_yday = 0;
          Unix.tm_isdst = false })

let dostime_of_unixtime t =
  let tm = Unix.localtime t in
  (tm.Unix.tm_sec lsr 1
     + (tm.Unix.tm_min lsl 5)
     + (tm.Unix.tm_hour lsl 11),
   tm.Unix.tm_mday
     + (tm.Unix.tm_mon + 1) lsl 5
     + (tm.Unix.tm_year - 80) lsl 9)

(* Read end of central directory record *)

let read_ecd filename ic =
  let buf = Bytes.create 256 in
  let filelen = LargeFile.in_channel_length ic in
  let rec find_ecd pos len =
    (* On input, bytes 0 ... len - 1 of buf reflect what is at pos in ic *)
    if pos <= 0L || Int64.sub filelen pos >= 0x10000L then
      raise (Error(filename, "",
                   "end of central directory not found, not a ZIP file"));
    let toread = if pos >= 128L then 128 else Int64.to_int pos in
    (* Make room for "toread" extra bytes, and read them *)
    Bytes.blit buf 0 buf toread (256 - toread);
    let newpos = Int64.(sub pos (of_int toread)) in
    LargeFile.seek_in ic newpos;
    really_input ic buf 0 toread;
    let newlen = min (toread + len) 256 in
    (* Search for magic number *)
    let ofs = strrstr "PK\005\006" buf 0 newlen in
    if ofs < 0 || newlen < 22 ||
       (let comment_len =
              (Char.code (Bytes.get buf (ofs + 20)))
          lor ((Char.code (Bytes.get buf (ofs + 21))) lsl 8) in
        Int64.(add newpos (of_int (ofs + 22 + comment_len))) <> filelen) then
      find_ecd newpos newlen
    else
      Int64.(add newpos (of_int ofs)) in
  LargeFile.seek_in ic (find_ecd filelen 0);
  let magic = read4 ic in
  let disk_no = read2 ic in
  let cd_disk_no = read2 ic in
  let _disk_entries = read2 ic in
  let cd_entries = read2 ic in
  let cd_size = read4 ic in
  let cd_offset = read4 ic in
  let comment_len = read2 ic in
  let comment = readstring ic comment_len in
  assert (magic = Int32.of_int 0x06054b50);
  if disk_no <> 0 || cd_disk_no <> 0 then
    raise (Error(filename, "", "multi-disk ZIP files not supported"));
  (cd_entries, cd_size, cd_offset, comment)

(* Read central directory *)

let int64_of_uint32 n =
  Int64.(logand (of_int32 n) 0xFFFF_FFFFL)

let read_cd filename ic cd_entries cd_offset cd_bound =
  let cd_bound = int64_of_uint32 cd_bound in
  try
    LargeFile.seek_in ic (int64_of_uint32 cd_offset);
    let e = ref [] in
    let entrycnt = ref 0 in
    while (LargeFile.pos_in ic < cd_bound) do
      incr entrycnt;
      let magic = read4 ic in
      let _version_made_by = read2 ic in
      let _version_needed = read2 ic in
      let flags = read2 ic in
      let methd = read2 ic in
      let lastmod_time = read2 ic in
      let lastmod_date = read2 ic in
      let crc = read4 ic in
      let compr_size = read4_int ic in
      let uncompr_size = read4_int ic in
      let name_len = read2 ic in
      let extra_len = read2 ic in
      let comment_len = read2 ic in
      let _disk_number = read2 ic in
      let _internal_attr = read2 ic in
      let _external_attr = read4 ic in
      let header_offset = int64_of_uint32 (read4 ic) in
      let name = readstring ic name_len in
      let extra = readstring ic extra_len in
      let comment = readstring ic comment_len in
      if magic <> Int32.of_int 0x02014b50 then
        raise (Error(filename, name,
                     "wrong file header in central directory"));
      if flags land 1 <> 0 then
        raise (Error(filename, name, "encrypted entries not supported"));
      if methd <> 0 then
        raise (Error(filename, name, "unknown compression method"));
      e := { filename = name;
             extra = extra;
             comment = comment;
             mtime = unixtime_of_dostime lastmod_time lastmod_date;
             crc = crc;
             uncompressed_size = uncompr_size;
             compressed_size = compr_size;
             is_directory = filename_is_directory name;
             file_offset = header_offset
           } :: !e
    done;
    assert((cd_bound = (LargeFile.pos_in ic)) &&
           (cd_entries = 65535 || cd_entries = !entrycnt land 0xffff));
    List.rev !e
  with End_of_file ->
    raise (Error(filename, "", "end-of-file while reading central directory"))

(* Open a ZIP file for reading *)

let open_in filename =
  let ic = Pervasives.open_in_bin filename in
  try
    let (cd_entries, cd_size, cd_offset, cd_comment) = read_ecd filename ic in
    let entries =
      read_cd filename ic cd_entries cd_offset (Int32.add cd_offset cd_size) in
    let dir = Hashtbl.create (cd_entries / 3) in
    List.iter (fun e -> Hashtbl.add dir e.filename e) entries;
    { if_filename = filename;
      if_channel = ic;
      if_entries = entries;
      if_directory = dir;
      if_comment = cd_comment }
  with exn ->
    Pervasives.close_in ic; raise exn

(* Close a ZIP file opened for reading *)

let close_in ifile =
  Pervasives.close_in ifile.if_channel

(* Return the info associated with an entry *)

let find_entry ifile name =
  Hashtbl.find ifile.if_directory name

(* Position on an entry *)

let goto_entry ifile e =
  try
    let ic = ifile.if_channel in
    LargeFile.seek_in ic e.file_offset;
    let magic = read4 ic in
    let _version_needed = read2 ic in
    let _flags = read2 ic in
    let _methd = read2 ic in
    let _lastmod_time = read2 ic in
    let _lastmod_date = read2 ic in
    let _crc = read4 ic in
    let _compr_size = read4_int ic in
    let _uncompr_size = read4_int ic in
    let filename_len = read2 ic in
    let extra_len = read2 ic in
    if magic <> Int32.of_int 0x04034b50 then
       raise (Error(ifile.if_filename, e.filename, "wrong local file header"));
    (* Could validate information read against directory entry, but
       what the heck *)
    LargeFile.seek_in ifile.if_channel
      (Int64.add e.file_offset (Int64.of_int (30 + filename_len + extra_len)))
  with End_of_file ->
    raise (Error(ifile.if_filename, e.filename, "truncated local file header"))

(* Read the contents of an entry as a string *)

let seek_entry ifile e =
  try
    goto_entry ifile e;
    if e.compressed_size <> e.uncompressed_size then
      raise (Error(ifile.if_filename, e.filename,
                    "wrong size for stored entry"));
    ifile.if_channel
  with End_of_file ->
    raise (Error(ifile.if_filename, e.filename, "truncated data"))

(* Open a ZIP file for writing *)

let open_out ?(comment = "") filename =
  if String.length comment >= 0x10000 then
    raise(Error(filename, "", "comment too long"));
  { of_filename = filename;
    of_channel = Pervasives.open_out_bin filename;
    of_entries = [];
    of_comment = comment }

(* Close a ZIP file for writing.  Add central directory. *)

let write_directory_entry oc e =
  write4 oc (Int32.of_int 0x02014b50);  (* signature *)
  let version = 10 in
  write2 oc version;                    (* version made by *)
  write2 oc version;                    (* version needed to extract *)
  write2 oc 8;                          (* flags *)
  write2 oc 0;                          (* method *)
  let (time, date) = dostime_of_unixtime e.mtime in
  write2 oc time;                       (* last mod time *)
  write2 oc date;                       (* last mod date *)
  write4 oc e.crc;                      (* CRC32 *)
  write4_int oc e.compressed_size;      (* compressed size *)
  write4_int oc e.uncompressed_size;    (* uncompressed size *)
  write2 oc (String.length e.filename); (* filename length *)
  write2 oc (String.length e.extra);    (* extra length *)
  write2 oc (String.length e.comment);  (* comment length *)
  write2 oc 0;                          (* disk number start *)
  write2 oc 0;                          (* internal attributes *)
  write4_int oc 0;                      (* external attributes *)
  write4 oc (Int64.to_int32 e.file_offset); (* offset of local header *)
  writestring oc e.filename;            (* filename *)
  writestring oc e.extra;               (* extra info *)
  writestring oc e.comment              (* file comment *)

let close_out ofile =
  let oc = ofile.of_channel in
  let start_cd = pos_out oc in
  List.iter (write_directory_entry oc) (List.rev ofile.of_entries);
  let cd_size = pos_out oc - start_cd in
  let num_entries = List.length ofile.of_entries in
  if num_entries >= 0x10000 then
    raise(Error(ofile.of_filename, "", "too many entries"));
  write4 oc (Int32.of_int 0x06054b50);  (* signature *)
  write2 oc 0;                          (* disk number *)
  write2 oc 0;                          (* number of disk with central dir *)
  write2 oc num_entries;                (* # entries in this disk *)
  write2 oc num_entries;                (* # entries in central dir *)
  write4_int oc cd_size;                (* size of central dir *)
  write4_int oc start_cd;               (* offset of central dir *)
  write2 oc (String.length ofile.of_comment); (* length of comment *)
  writestring oc ofile.of_comment;         (* comment *)
  Pervasives.close_out oc

(* Write a local file header and return the corresponding entry *)

let add_entry_header ofile extra comment mtime filename =
  if String.length filename >= 0x10000 then
    raise(Error(ofile.of_filename, filename, "filename too long"));
  if String.length extra >= 0x10000 then
    raise(Error(ofile.of_filename, filename, "extra data too long"));
  if String.length comment >= 0x10000 then
    raise(Error(ofile.of_filename, filename, "comment too long"));
  let oc = ofile.of_channel in
  let pos = LargeFile.pos_out oc in
  write4 oc (Int32.of_int 0x04034b50);  (* signature *)
  let version = 10 in
  write2 oc version;                    (* version needed to extract *)
  write2 oc 8;                          (* flags *)
  write2 oc 0; (* method *)
  let (time, date) = dostime_of_unixtime mtime in
  write2 oc time;                       (* last mod time *)
  write2 oc date;                       (* last mod date *)
  write4 oc Int32.zero;                 (* CRC32 - to be filled later *)
  write4_int oc 0;                      (* compressed size - later *)
  write4_int oc 0;                      (* uncompressed size - later *)
  write2 oc (String.length filename);   (* filename length *)
  write2 oc (String.length extra);      (* extra length *)
  writestring oc filename;              (* filename *)
  writestring oc extra;                 (* extra info *)
  { filename = filename;
    extra = extra;
    comment = comment;
    mtime = mtime;
    crc = Int32.zero;
    uncompressed_size = 0;
    compressed_size = 0;
    is_directory = filename_is_directory filename;
    file_offset = pos }

(* Write a data descriptor and update the entry *)

let add_data_descriptor ofile crc compr_size uncompr_size entry =
  let oc = ofile.of_channel in
  write4 oc (Int32.of_int 0x08074b50);  (* signature *)
  write4 oc crc;                        (* CRC *)
  write4_int oc compr_size;             (* compressed size *)
  write4_int oc uncompr_size;           (* uncompressed size *)
  { entry with crc = crc;
               uncompressed_size = uncompr_size;
               compressed_size = compr_size }

(* Add an entry with the contents of a string *)

let add_entry data ofile ?(extra = "") ?(comment = "")
                         ?(mtime = Unix.time()) name =
  let e = add_entry_header ofile extra comment mtime name in
  let crc = update_crc_string Int32.zero data 0 (String.length data) in
  let compr_size =
        output_substring ofile.of_channel data 0 (String.length data);
        String.length data
  in
  let e' = add_data_descriptor ofile crc compr_size (String.length data) e in
  ofile.of_entries <- e' :: ofile.of_entries

(* Add an entry with the contents of an in channel *)

let copy_channel_to_entry ic ofile ?(extra = "") ?(comment = "")
                                   ?(mtime = Unix.time()) name =
  let e = add_entry_header ofile extra comment mtime name in
  let crc = ref Int32.zero in
  let (compr_size, uncompr_size) =
        let buf = Bytes.create 4096 in
        let rec copy sz =
          let r = input ic buf 0 (Bytes.length buf) in
          if r = 0 then sz else begin
            crc := update_crc !crc buf 0 r;
            output ofile.of_channel buf 0 r;
            copy (sz + r)
          end in
        let size = copy 0 in
        (size, size)
  in
  let e' = add_data_descriptor ofile !crc compr_size uncompr_size e in
  ofile.of_entries <- e' :: ofile.of_entries
