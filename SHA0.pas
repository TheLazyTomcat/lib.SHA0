{-------------------------------------------------------------------------------

  This Source Code Form is subject to the terms of the Mozilla Public
  License, v. 2.0. If a copy of the MPL was not distributed with this
  file, You can obtain one at http://mozilla.org/MPL/2.0/.

-------------------------------------------------------------------------------}
{===============================================================================

  SHA0 Hash Calculation

  ©František Milt 2015-03-16

  Version 1.0

===============================================================================}
unit SHA0;

{$DEFINE LargeBuffer}
{.$DEFINE UseStringStream}

interface

uses
  Classes;

type
{$IFDEF x64}
  TSize = UInt64;
{$ELSE}
  TSize = LongWord;
{$ENDIF}

  TSHA0Hash = Record
    PartA:  LongWord;
    PartB:  LongWord;
    PartC:  LongWord;
    PartD:  LongWord;
    PartE:  LongWord;
  end;
  PSHA0Hash = ^TSHA0Hash;

const
  InitialSHA0: TSHA0Hash = (
    PartA:  $67452301;
    PartB:  $EFCDAB89;
    PartC:  $98BADCFE;
    PartD:  $10325476;
    PartE:  $C3D2E1F0);

  ZeroSHA0: TSHA0Hash = (PartA: 0; PartB: 0; PartC: 0; PartD: 0; PartE: 0);

Function SHA0toStr(Hash: TSHA0Hash): String;
Function StrToSHA0(Str: String): TSHA0Hash;
Function TryStrToSHA0(const Str: String; out Hash: TSHA0Hash): Boolean;
Function StrToSHA0Def(const Str: String; Default: TSHA0Hash): TSHA0Hash;
Function SameSHA0(A,B: TSHA0Hash): Boolean;

procedure BufferSHA0(var Hash: TSHA0Hash; const Buffer; Size: TSize); overload;
Function LastBufferSHA0(Hash: TSHA0Hash; const Buffer; Size: TSize; MessageSize: Int64 = -1): TSHA0Hash;

Function BufferSHA0(const Buffer; Size: TSize): TSHA0Hash; overload;

Function AnsiStringSHA0(const Str: AnsiString): TSHA0Hash;
Function WideStringSHA0(const Str: WideString): TSHA0Hash;
Function StringSHA0(const Str: String): TSHA0Hash;

Function StreamSHA0(Stream: TStream; Count: Int64 = -1): TSHA0Hash;
Function FileSHA0(const FileName: String): TSHA0Hash;

//------------------------------------------------------------------------------

type
  TSHA0Context = type Pointer;

Function SHA0_Init: TSHA0Context;
procedure SHA0_Update(Context: TSHA0Context; const Buffer; Size: TSize);
Function SHA0_Final(var Context: TSHA0Context; const Buffer; Size: TSize): TSHA0Hash; overload;
Function SHA0_Final(var Context: TSHA0Context): TSHA0Hash; overload;
Function SHA0_Hash(const Buffer; Size: TSize): TSHA0Hash;


implementation

uses
  SysUtils, Math;

const
  BlockSize       = 64;                           // 512 bits
{$IFDEF LargeBuffers}
  BlocksPerBuffer = 16384;                        // 1MiB BufferSize
{$ELSE}
  BlocksPerBuffer = 64;                           // 4KiB BufferSize
{$ENDIF}
  BufferSize      = BlocksPerBuffer * BlockSize;  // size of read buffer

  RoundConsts: Array[0..3] of LongWord = ($5A827999, $6ED9EBA1, $8F1BBCDC, $CA62C1D6);

type
  TBlockBuffer = Array[0..BlockSize - 1] of Byte;

  TSHA0Context_Internal = record
    MessageHash:    TSHA0Hash;
    MessageSize:    Int64;
    TransferSize:   LongWord;
    TransferBuffer: TBlockBuffer;
  end;
  PSHA0Context_Internal = ^TSHA0Context_Internal;

//==============================================================================

{$IFDEF FPC}{$ASMMODE intel}{$ENDIF}

Function EndianSwap(Value: LongWord): LongWord;{$IFNDEF PurePascal}assembler;{$ENDIF} overload;
{$IFDEF PurePascal}
begin
Result := (Value and $000000FF shl 24) or (Value and $0000FF00 shl 8) or
          (Value and $00FF0000 shr 8) or (Value and $FF000000 shr 24);
end;
{$ELSE}
asm
{$IFDEF x64}
  MOV   RAX, RCX
{$ENDIF}
  BSWAP EAX
end;
{$ENDIF}
      
//------------------------------------------------------------------------------

Function EndianSwap(Value: Int64): Int64;{$IFNDEF PurePascal}assembler;{$ENDIF} overload;
{$IFDEF PurePascal}
begin
Int64Rec(Result).Hi := EndianSwap(Int64Rec(Value).Lo);
Int64Rec(Result).Lo := EndianSwap(Int64Rec(Value).Hi);
end;
{$ELSE}
asm
{$IFDEF x64}
  MOV   RAX, RCX
  BSWAP RAX
{$ELSE}
  MOV EAX, dword ptr [Value + 4]
  MOV EDX, dword ptr [Value]
  BSWAP EAX
  BSWAP EDX
{$ENDIF}
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function LeftRotate(Number,Shift: LongWord): LongWord; register; {$IFNDEF PurePascal}assembler;{$ENDIF}
{$IFDEF PurePascal}
begin
  Result := (Number shl Shift) or (Number shr (32 - Shift));
end;
{$ELSE}
{$IFDEF FPC}{$ASMMODE intel}{$ENDIF}
asm
{$IFDEF x64}
  MOV   EAX,  ECX
{$ENDIF}
  MOV   CL,   DL
  ROL   EAX,  CL
end;
{$ENDIF}

//==============================================================================

Function BlockHash(Hash: TSHA0Hash; const Block): TSHA0Hash;
var
  i:              Integer;
  Temp:           LongWord;
  FuncResult:     LongWord;
  RoundConstant:  LongWord;
  State:          Array[0..79] of LongWord;  
  BlockWords:     Array[0..15] of LongWord absolute Block;
begin
Result := Hash;
For i := 0 to 15 do State[i] := EndianSwap(BlockWords[i]);
For i := 16 to 79 do State[i] := State[i - 3] xor State[i - 8] xor State[i - 14] xor State[i - 16];
For i := 0 to 79 do
  begin
    case i of
       0..19: begin
                FuncResult := (Hash.PartB and Hash.PartC) or ((not Hash.PartB) and Hash.PartD);
                RoundConstant := RoundConsts[0];
              end;
      20..39: begin
                FuncResult := Hash.PartB xor Hash.PartC xor Hash.PartD;
                RoundConstant := RoundConsts[1];
              end;
      40..59: begin
                FuncResult := (Hash.PartB and Hash.PartC) or (Hash.PartB and Hash.PartD) or (Hash.PartC and Hash.PartD);
                RoundConstant := RoundConsts[2];
              end;
    else
     {60..79:}  FuncResult := Hash.PartB xor Hash.PartC xor Hash.PartD;
                RoundConstant := RoundConsts[3];
    end;
    Temp := LeftRotate(Hash.PartA,5) + FuncResult + Hash.PartE + RoundConstant + State[i];
    Hash.PartE := Hash.PartD;
    Hash.PartD := Hash.PartC;
    Hash.PartC := LeftRotate(Hash.PartB,30);
    Hash.PartB := Hash.PartA;
    Hash.PartA := Temp;
  end;
Inc(Result.PartA,Hash.PartA);
Inc(Result.PartB,Hash.PartB);
Inc(Result.PartC,Hash.PartC);
Inc(Result.PartD,Hash.PartD);
Inc(Result.PartE,Hash.PartE);
end;

//==============================================================================

Function SHA0toStr(Hash: TSHA0Hash): String;
begin
Result := IntToHex(Hash.PartA,8) + IntToHex(Hash.PartB,8) +
          IntToHex(Hash.PartC,8) + IntToHex(Hash.PartD,8) +
          IntToHex(Hash.PartE,8);
end;

//------------------------------------------------------------------------------

Function StrToSHA0(Str: String): TSHA0Hash;
begin
If Length(Str) < 40 then
  Str := StringOfChar('0',40 - Length(Str)) + Str
else
  If Length(Str) > 40 then
    Str := Copy(Str,Length(Str) - 39,40);
Result.PartA := StrToInt('$' + Copy(Str,1,8));
Result.PartB := StrToInt('$' + Copy(Str,9,8));
Result.PartC := StrToInt('$' + Copy(Str,17,8));
Result.PartD := StrToInt('$' + Copy(Str,25,8));
Result.PartE := StrToInt('$' + Copy(Str,33,8));
end;

//------------------------------------------------------------------------------

Function TryStrToSHA0(const Str: String; out Hash: TSHA0Hash): Boolean;
begin
try
  Hash := StrToSHA0(Str);
  Result := True;
except
  Result := False;
end;
end;

//------------------------------------------------------------------------------

Function StrToSHA0Def(const Str: String; Default: TSHA0Hash): TSHA0Hash;
begin
If not TryStrToSHA0(Str,Result) then
  Result := Default;
end;

//------------------------------------------------------------------------------

Function SameSHA0(A,B: TSHA0Hash): Boolean;
begin
Result := (A.PartA = B.PartA) and (A.PartB = B.PartB) and
          (A.PartC = B.PartC) and (A.PartD = B.PartD) and
          (A.PartE = B.PartE);
end;

//==============================================================================

procedure BufferSHA0(var Hash: TSHA0Hash; const Buffer; Size: TSize);
type
  TBlocksArray = Array[0..0] of TBlockBuffer;
var
  i:  Integer;
begin
If (Size mod BlockSize) = 0 then
  begin
    For i := 0 to Pred(Size div BlockSize) do
      Hash := BlockHash(Hash,TBlocksArray(Buffer)[i]);
  end
else raise Exception.CreateFmt('BufferSHA0: Buffer size is not divisible by %d.',[BlockSize]);
end;

//------------------------------------------------------------------------------

Function LastBufferSHA0(Hash: TSHA0Hash; const Buffer; Size: TSize; MessageSize: Int64 = -1): TSHA0Hash;
type
  TInt64Array = Array[0..0] of Int64;
var
  FullBlocks:     Integer;
  LastBlockSize:  Integer;
  HelpBlocks:     Integer;
  HelpBlocksBuff: Pointer;
begin
Result := Hash;
If MessageSize < 0 then MessageSize := Size;
FullBlocks := Size div BlockSize;
If FullBlocks > 0 then BufferSHA0(Result,Buffer,FullBlocks * BlockSize);
LastBlockSize := Size - TSize(FullBlocks * BlockSize);
HelpBlocks := Ceil((LastBlockSize + SizeOf(Int64) + 1) / BlockSize);
HelpBlocksBuff := AllocMem(HelpBlocks * BlockSize);
try
  Move(TByteArray(Buffer)[FullBlocks * BlockSize],HelpBlocksBuff^,LastBlockSize);
  TByteArray(HelpBlocksBuff^)[LastBlockSize] := $80;
  TInt64Array(HelpBlocksBuff^)[HelpBlocks * (BlockSize div SizeOf(Int64)) - 1] := EndianSwap(MessageSize * 8);
  BufferSHA0(Result,HelpBlocksBuff^,HelpBlocks * BlockSize);
finally
  FreeMem(HelpBlocksBuff,HelpBlocks * BlockSize);
end;
end;

//==============================================================================

Function BufferSHA0(const Buffer; Size: TSize): TSHA0Hash;
begin
Result := LastBufferSHA0(InitialSHA0,Buffer,Size);
end;

//==============================================================================

Function AnsiStringSHA0(const Str: AnsiString): TSHA0Hash;
{$IFDEF UseStringStream}
var
  StringStream: TStringStream;
begin
StringStream := TStringStream.Create(Str);
try
  Result := StreamSHA0(StringStream);
finally
  StringStream.Free;
end;
end;
{$ELSE}
begin
Result := BufferSHA0(PAnsiChar(Str)^,Length(Str) * SizeOf(AnsiChar));
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function WideStringSHA0(const Str: WideString): TSHA0Hash;
{$IFDEF UseStringStream}
var
  StringStream: TStringStream;
begin
StringStream := TStringStream.Create(Str);
try
  Result := StreamSHA0(StringStream);
finally
  StringStream.Free;
end;
end;
{$ELSE}
begin
Result := BufferSHA0(PWideChar(Str)^,Length(Str) * SizeOf(WideChar));
end;
{$ENDIF}

//------------------------------------------------------------------------------

Function StringSHA0(const Str: String): TSHA0Hash;
{$IFDEF UseStringStream}
var
  StringStream: TStringStream;
begin
StringStream := TStringStream.Create(Str);
try
  Result := StreamSHA0(StringStream);
finally
  StringStream.Free;
end;
end;
{$ELSE}
begin
Result := BufferSHA0(PChar(Str)^,Length(Str) * SizeOf(Char));
end;
{$ENDIF}

//==============================================================================

Function StreamSHA0(Stream: TStream; Count: Int64 = -1): TSHA0Hash;
var
  Buffer:       Pointer;
  BytesRead:    Integer;
  MessageSize:  Int64;
begin
If Assigned(Stream) then
  begin
    If Count = 0 then
      Count := Stream.Size - Stream.Position;
    If Count < 0 then
      begin
        Stream.Position := 0;
        Count := Stream.Size;
      end;
    MessageSize := Count;
    GetMem(Buffer,BufferSize);
    try
      Result := InitialSHA0;
      repeat
        BytesRead := Stream.Read(Buffer^,Min(BufferSize,Count));
        If BytesRead < BufferSize then
          Result := LastBufferSHA0(Result,Buffer^,BytesRead,MessageSize)
        else
          BufferSHA0(Result,Buffer^,BytesRead);
        Dec(Count,BytesRead);
      until BytesRead < BufferSize;
    finally
      FreeMem(Buffer,BufferSize);
    end;
  end
else raise Exception.Create('StreamSHA0: Stream is not assigned.');
end;

//------------------------------------------------------------------------------

Function FileSHA0(const FileName: String): TSHA0Hash;
var
  FileStream: TFileStream;
begin
FileStream := TFileStream.Create(FileName, fmOpenRead or fmShareDenyWrite);
try
  Result := StreamSHA0(FileStream);
finally
  FileStream.Free;
end;
end;

//==============================================================================

Function SHA0_Init: TSHA0Context;
begin
Result := AllocMem(SizeOf(TSHA0Context_Internal));
with PSHA0Context_Internal(Result)^ do
  begin
    MessageHash := InitialSHA0;
    MessageSize := 0;
    TransferSize := 0;
  end;
end;

//------------------------------------------------------------------------------

procedure SHA0_Update(Context: TSHA0Context; const Buffer; Size: TSize);
var
  FullChunks:     Integer;
  RemainingSize:  TSize;
begin
with PSHA0Context_Internal(Context)^ do
  begin
    If TransferSize > 0 then
      begin
        If Size >= (BlockSize - TransferSize) then
          begin
            Inc(MessageSize,BlockSize - TransferSize);
            Move(Buffer,TransferBuffer[TransferSize],BlockSize - TransferSize);
            BufferSHA0(MessageHash,TransferBuffer,BlockSize);
            RemainingSize := Size - (BlockSize - TransferSize);
            TransferSize := 0;
            SHA0_Update(Context,TByteArray(Buffer)[Size - RemainingSize],RemainingSize);
          end
        else
          begin
            Inc(MessageSize,Size);
            Move(Buffer,TransferBuffer[TransferSize],Size);
            Inc(TransferSize,Size);
          end;  
      end
    else
      begin
        Inc(MessageSize,Size);
        FullChunks := Size div BlockSize;
        BufferSHA0(MessageHash,Buffer,FullChunks * BlockSize);
        If TSize(FullChunks * BlockSize) < Size then
          begin
            TransferSize := Size - TSize(FullChunks * BlockSize);
            Move(TByteArray(Buffer)[Size - TransferSize],TransferBuffer,TransferSize);
          end;
      end;
  end;
end;

//------------------------------------------------------------------------------

Function SHA0_Final(var Context: TSHA0Context; const Buffer; Size: TSize): TSHA0Hash;
begin
SHA0_Update(Context,Buffer,Size);
Result := SHA0_Final(Context);
end;

//------------------------------------------------------------------------------

Function SHA0_Final(var Context: TSHA0Context): TSHA0Hash;
begin
with PSHA0Context_Internal(Context)^ do
  Result := LastBufferSHA0(MessageHash,TransferBuffer,TransferSize,MessageSize);
FreeMem(Context,SizeOf(TSHA0Context_Internal));
Context := nil;
end;

//------------------------------------------------------------------------------

Function SHA0_Hash(const Buffer; Size: TSize): TSHA0Hash;
begin
Result := LastBufferSHA0(InitialSHA0,Buffer,Size);
end;

end.
