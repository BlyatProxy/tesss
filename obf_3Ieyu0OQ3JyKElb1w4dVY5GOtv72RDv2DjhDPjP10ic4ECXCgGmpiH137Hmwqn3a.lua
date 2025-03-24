--[[
 .____                  ________ ___.    _____                           __                
 |    |    __ _______   \_____  \\_ |___/ ____\_ __  ______ ____ _____ _/  |_  ___________ 
 |    |   |  |  \__  \   /   |   \| __ \   __\  |  \/  ___// ___\\__  \\   __\/  _ \_  __ \
 |    |___|  |  // __ \_/    |    \ \_\ \  | |  |  /\___ \\  \___ / __ \|  | (  <_> )  | \/
 |_______ \____/(____  /\_______  /___  /__| |____//____  >\___  >____  /__|  \____/|__|   
         \/          \/         \/    \/                \/     \/     \/                   
          \_Welcome to LuaObfuscator.com   (Alpha 0.10.8) ~  Much Love, Ferib 

]]--

local StrToNumber = tonumber;
local Byte = string.byte;
local Char = string.char;
local Sub = string.sub;
local Subg = string.gsub;
local Rep = string.rep;
local Concat = table.concat;
local Insert = table.insert;
local LDExp = math.ldexp;
local GetFEnv = getfenv or function()
	return _ENV;
end;
local Setmetatable = setmetatable;
local PCall = pcall;
local Select = select;
local Unpack = unpack or table.unpack;
local ToNumber = tonumber;
local function VMCall(ByteString, vmenv, ...)
	local DIP = 1;
	local repeatNext;
	ByteString = Subg(Sub(ByteString, 5), "..", function(byte)
		if (Byte(byte, 2) == 81) then
			repeatNext = StrToNumber(Sub(byte, 1, 1));
			return "";
		else
			local a = Char(StrToNumber(byte, 16));
			if repeatNext then
				local b = Rep(a, repeatNext);
				repeatNext = nil;
				return b;
			else
				return a;
			end
		end
	end);
	local function gBit(Bit, Start, End)
		if End then
			local Res = (Bit / (2 ^ (Start - 1))) % (2 ^ (((End - 1) - (Start - 1)) + 1));
			return Res - (Res % 1);
		else
			local Plc = 2 ^ (Start - 1);
			return (((Bit % (Plc + Plc)) >= Plc) and 1) or 0;
		end
	end
	local function gBits8()
		local a = Byte(ByteString, DIP, DIP);
		DIP = DIP + 1;
		return a;
	end
	local function gBits16()
		local a, b = Byte(ByteString, DIP, DIP + 2);
		DIP = DIP + 2;
		return (b * 256) + a;
	end
	local function gBits32()
		local a, b, c, d = Byte(ByteString, DIP, DIP + 3);
		DIP = DIP + 4;
		return (d * 16777216) + (c * 65536) + (b * 256) + a;
	end
	local function gFloat()
		local Left = gBits32();
		local Right = gBits32();
		local IsNormal = 1;
		local Mantissa = (gBit(Right, 1, 20) * (2 ^ 32)) + Left;
		local Exponent = gBit(Right, 21, 31);
		local Sign = ((gBit(Right, 32) == 1) and -1) or 1;
		if (Exponent == 0) then
			if (Mantissa == 0) then
				return Sign * 0;
			else
				Exponent = 1;
				IsNormal = 0;
			end
		elseif (Exponent == 2047) then
			return ((Mantissa == 0) and (Sign * (1 / 0))) or (Sign * NaN);
		end
		return LDExp(Sign, Exponent - 1023) * (IsNormal + (Mantissa / (2 ^ 52)));
	end
	local function gString(Len)
		local Str;
		if not Len then
			Len = gBits32();
			if (Len == 0) then
				return "";
			end
		end
		Str = Sub(ByteString, DIP, (DIP + Len) - 1);
		DIP = DIP + Len;
		local FStr = {};
		for Idx = 1, #Str do
			FStr[Idx] = Char(Byte(Sub(Str, Idx, Idx)));
		end
		return Concat(FStr);
	end
	local gInt = gBits32;
	local function _R(...)
		return {...}, Select("#", ...);
	end
	local function Deserialize()
		local Instrs = {};
		local Functions = {};
		local Lines = {};
		local Chunk = {Instrs,Functions,nil,Lines};
		local ConstCount = gBits32();
		local Consts = {};
		for Idx = 1, ConstCount do
			local Type = gBits8();
			local Cons;
			if (Type == 1) then
				Cons = gBits8() ~= 0;
			elseif (Type == 2) then
				Cons = gFloat();
			elseif (Type == 3) then
				Cons = gString();
			end
			Consts[Idx] = Cons;
		end
		Chunk[3] = gBits8();
		for Idx = 1, gBits32() do
			local Descriptor = gBits8();
			if (gBit(Descriptor, 1, 1) == 0) then
				local Type = gBit(Descriptor, 2, 3);
				local Mask = gBit(Descriptor, 4, 6);
				local Inst = {gBits16(),gBits16(),nil,nil};
				if (Type == 0) then
					Inst[3] = gBits16();
					Inst[4] = gBits16();
				elseif (Type == 1) then
					Inst[3] = gBits32();
				elseif (Type == 2) then
					Inst[3] = gBits32() - (2 ^ 16);
				elseif (Type == 3) then
					Inst[3] = gBits32() - (2 ^ 16);
					Inst[4] = gBits16();
				end
				if (gBit(Mask, 1, 1) == 1) then
					Inst[2] = Consts[Inst[2]];
				end
				if (gBit(Mask, 2, 2) == 1) then
					Inst[3] = Consts[Inst[3]];
				end
				if (gBit(Mask, 3, 3) == 1) then
					Inst[4] = Consts[Inst[4]];
				end
				Instrs[Idx] = Inst;
			end
		end
		for Idx = 1, gBits32() do
			Functions[Idx - 1] = Deserialize();
		end
		return Chunk;
	end
	local function Wrap(Chunk, Upvalues, Env)
		local Instr = Chunk[1];
		local Proto = Chunk[2];
		local Params = Chunk[3];
		return function(...)
			local Instr = Instr;
			local Proto = Proto;
			local Params = Params;
			local _R = _R;
			local VIP = 1;
			local Top = -1;
			local Vararg = {};
			local Args = {...};
			local PCount = Select("#", ...) - 1;
			local Lupvals = {};
			local Stk = {};
			for Idx = 0, PCount do
				if (Idx >= Params) then
					Vararg[Idx - Params] = Args[Idx + 1];
				else
					Stk[Idx] = Args[Idx + 1];
				end
			end
			local Varargsz = (PCount - Params) + 1;
			local Inst;
			local Enum;
			while true do
				Inst = Instr[VIP];
				Enum = Inst[1];
				if (Enum <= 210) then
					if (Enum <= 104) then
						if (Enum <= 51) then
							if (Enum <= 25) then
								if (Enum <= 12) then
									if (Enum <= 5) then
										if (Enum <= 2) then
											if (Enum <= 0) then
												local A = Inst[2];
												Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											elseif (Enum > 1) then
												local A;
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Env[Inst[3]];
											else
												local A;
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A](Unpack(Stk, A + 1, Inst[3]));
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Env[Inst[3]];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Inst[3];
												VIP = VIP + 1;
												Inst = Instr[VIP];
												A = Inst[2];
												Stk[A](Stk[A + 1]);
												VIP = VIP + 1;
												Inst = Instr[VIP];
												Stk[Inst[2]] = Env[Inst[3]];
											end
										elseif (Enum <= 3) then
											local A;
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Env[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A]();
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Env[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										elseif (Enum > 4) then
											if (Stk[Inst[2]] <= Stk[Inst[4]]) then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local A;
											Env[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
									elseif (Enum <= 8) then
										if (Enum <= 6) then
											local A;
											Env[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Stk[A + 1]);
										elseif (Enum > 7) then
											local A;
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										else
											local A;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											VIP = Inst[3];
										end
									elseif (Enum <= 10) then
										if (Enum == 9) then
											local A = Inst[2];
											local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
											Top = (Limit + A) - 1;
											local Edx = 0;
											for Idx = A, Top do
												Edx = Edx + 1;
												Stk[Idx] = Results[Edx];
											end
										else
											Env[Inst[3]] = Stk[Inst[2]];
										end
									elseif (Enum == 11) then
										local A;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									else
										local A;
										local K;
										local B;
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 18) then
									if (Enum <= 15) then
										if (Enum <= 13) then
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
										elseif (Enum > 14) then
											local A;
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
										else
											local K;
											local B;
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return Stk[Inst[2]];
											end
										end
									elseif (Enum <= 16) then
										local B;
										local A;
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 17) then
										if (Stk[Inst[2]] <= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										local K;
										local B;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum <= 21) then
									if (Enum <= 19) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = #Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									elseif (Enum == 20) then
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum <= 23) then
									if (Enum == 22) then
										local K;
										local B;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] == Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum > 24) then
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								else
									local Edx;
									local Results;
									local B;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 38) then
								if (Enum <= 31) then
									if (Enum <= 28) then
										if (Enum <= 26) then
											Upvalues[Inst[3]] = Stk[Inst[2]];
										elseif (Enum > 27) then
											Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return Stk[Inst[2]];
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										else
											Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										end
									elseif (Enum <= 29) then
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									elseif (Enum == 30) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Upvalues[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local A;
										local K;
										local B;
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									end
								elseif (Enum <= 34) then
									if (Enum <= 32) then
										local A;
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									elseif (Enum == 33) then
										local B;
										local A;
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									end
								elseif (Enum <= 36) then
									if (Enum > 35) then
										if (Inst[2] == Stk[Inst[4]]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
									end
								elseif (Enum == 37) then
									local B;
									local T;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								else
									local K;
									local Edx;
									local Results, Limit;
									local B;
									local A;
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 44) then
								if (Enum <= 41) then
									if (Enum <= 39) then
										local A;
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 40) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local A;
										local K;
										local B;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 42) then
									local A;
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
								elseif (Enum == 43) then
									Stk[Inst[2]][Inst[3]] = Inst[4];
								else
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 47) then
								if (Enum <= 45) then
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 46) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 49) then
								if (Enum > 48) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A = Inst[2];
									local B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
								end
							elseif (Enum == 50) then
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local B;
								local A;
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 77) then
							if (Enum <= 64) then
								if (Enum <= 57) then
									if (Enum <= 54) then
										if (Enum <= 52) then
											local A;
											local K;
											local B;
											Stk[Inst[2]] = {};
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										elseif (Enum > 53) then
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = not Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Upvalues[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										else
											local A;
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3] ~= 0;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
										end
									elseif (Enum <= 55) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
									elseif (Enum > 56) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
									else
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] ~= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 60) then
									if (Enum <= 58) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									elseif (Enum > 59) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
									else
										local B;
										local T;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										T = Stk[A];
										B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									end
								elseif (Enum <= 62) then
									if (Enum == 61) then
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									else
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum > 63) then
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Stk[Inst[2]] ~= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum <= 70) then
								if (Enum <= 67) then
									if (Enum <= 65) then
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Inst[3]));
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										do
											return Unpack(Stk, A, Top);
										end
									elseif (Enum > 66) then
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local K;
										local B;
										local A;
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum <= 68) then
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
								elseif (Enum == 69) then
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 73) then
								if (Enum <= 71) then
									local A;
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum > 72) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local B;
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 75) then
								if (Enum == 74) then
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 76) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 90) then
							if (Enum <= 83) then
								if (Enum <= 80) then
									if (Enum <= 78) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									elseif (Enum == 79) then
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
									else
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
									end
								elseif (Enum <= 81) then
									local A = Inst[2];
									local Step = Stk[A + 2];
									local Index = Stk[A] + Step;
									Stk[A] = Index;
									if (Step > 0) then
										if (Index <= Stk[A + 1]) then
											VIP = Inst[3];
											Stk[A + 3] = Index;
										end
									elseif (Index >= Stk[A + 1]) then
										VIP = Inst[3];
										Stk[A + 3] = Index;
									end
								elseif (Enum > 82) then
									local A;
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local B;
									local A;
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 86) then
								if (Enum <= 84) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								elseif (Enum > 85) then
									local Edx;
									local Results;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 88) then
								if (Enum == 87) then
									do
										return;
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]];
								end
							elseif (Enum == 89) then
								Stk[Inst[2]] = Upvalues[Inst[3]];
							else
								local A = Inst[2];
								local Cls = {};
								for Idx = 1, #Lupvals do
									local List = Lupvals[Idx];
									for Idz = 0, #List do
										local Upv = List[Idz];
										local NStk = Upv[1];
										local DIP = Upv[2];
										if ((NStk == Stk) and (DIP >= A)) then
											Cls[DIP] = NStk[DIP];
											Upv[1] = Cls;
										end
									end
								end
							end
						elseif (Enum <= 97) then
							if (Enum <= 93) then
								if (Enum <= 91) then
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 92) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 95) then
								if (Enum == 94) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] ~= Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 96) then
								local Edx;
								local Results, Limit;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							end
						elseif (Enum <= 100) then
							if (Enum <= 98) then
								Stk[Inst[2]]();
							elseif (Enum == 99) then
								local A;
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 102) then
							if (Enum > 101) then
								local A = Inst[2];
								do
									return Unpack(Stk, A, A + Inst[3]);
								end
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum == 103) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Stk[Inst[2]] == Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum <= 157) then
						if (Enum <= 130) then
							if (Enum <= 117) then
								if (Enum <= 110) then
									if (Enum <= 107) then
										if (Enum <= 105) then
											local B;
											local A;
											Env[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											B = Stk[Inst[3]];
											Stk[A + 1] = B;
											Stk[A] = B[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										elseif (Enum > 106) then
											local A;
											local K;
											local B;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											do
												return Stk[A](Unpack(Stk, A + 1, Inst[3]));
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											do
												return Unpack(Stk, A, Top);
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										else
											Env[Inst[3]] = Stk[Inst[2]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
										end
									elseif (Enum <= 108) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
									elseif (Enum == 109) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if (Stk[Inst[2]] ~= Inst[4]) then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									else
										local A = Inst[2];
										do
											return Stk[A](Unpack(Stk, A + 1, Top));
										end
									end
								elseif (Enum <= 113) then
									if (Enum <= 111) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									elseif (Enum > 112) then
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										local A;
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 115) then
									if (Enum > 114) then
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									end
								elseif (Enum == 116) then
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 123) then
								if (Enum <= 120) then
									if (Enum <= 118) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									elseif (Enum > 119) then
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									else
										local A;
										local K;
										local B;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
									end
								elseif (Enum <= 121) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 122) then
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = not Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 126) then
								if (Enum <= 124) then
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Upvalues[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 125) then
									local B;
									local A;
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 128) then
								if (Enum == 127) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 129) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 143) then
							if (Enum <= 136) then
								if (Enum <= 133) then
									if (Enum <= 131) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									elseif (Enum == 132) then
										Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
									else
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 134) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum == 135) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								else
									local B;
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 139) then
								if (Enum <= 137) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 138) then
									local A;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 141) then
								if (Enum == 140) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum == 142) then
								local K;
								local B;
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 150) then
							if (Enum <= 146) then
								if (Enum <= 144) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
								elseif (Enum > 145) then
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								end
							elseif (Enum <= 148) then
								if (Enum > 147) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] < Stk[Inst[4]]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
								end
							elseif (Enum > 149) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 153) then
							if (Enum <= 151) then
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Enum > 152) then
								do
									return Stk[Inst[2]];
								end
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 155) then
							if (Enum == 154) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							end
						elseif (Enum == 156) then
							Stk[Inst[2]] = Wrap(Proto[Inst[3]], nil, Env);
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 183) then
						if (Enum <= 170) then
							if (Enum <= 163) then
								if (Enum <= 160) then
									if (Enum <= 158) then
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									elseif (Enum == 159) then
										Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
									else
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if not Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 161) then
									local A = Inst[2];
									local Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
									Top = (Limit + A) - 1;
									local Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								elseif (Enum == 162) then
									local Edx;
									local Results;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Stk[A + 1])};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local K;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 166) then
								if (Enum <= 164) then
									local K;
									local B;
									local A;
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								elseif (Enum == 165) then
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum <= 168) then
								if (Enum == 167) then
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum > 169) then
								local A;
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 176) then
							if (Enum <= 173) then
								if (Enum <= 171) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 172) then
									local K;
									local B;
									local A;
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Top))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum <= 174) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum == 175) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 179) then
							if (Enum <= 177) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							elseif (Enum == 178) then
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 181) then
							if (Enum == 180) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] ~= Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum == 182) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						else
							local B;
							local A;
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 196) then
						if (Enum <= 189) then
							if (Enum <= 186) then
								if (Enum <= 184) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								elseif (Enum > 185) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 187) then
								local A = Inst[2];
								local T = Stk[A];
								for Idx = A + 1, Top do
									Insert(T, Stk[Idx]);
								end
							elseif (Enum == 188) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local A;
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 192) then
							if (Enum <= 190) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum == 191) then
								local A;
								local K;
								local B;
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Inst[4]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 194) then
							if (Enum > 193) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local Edx;
								local Results, Limit;
								local K;
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 195) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
						end
					elseif (Enum <= 203) then
						if (Enum <= 199) then
							if (Enum <= 197) then
								local A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum > 198) then
								local Results;
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 201) then
							if (Enum > 200) then
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
							else
								local B;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							end
						elseif (Enum == 202) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						else
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						end
					elseif (Enum <= 206) then
						if (Enum <= 204) then
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum == 205) then
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							local A;
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 208) then
						if (Enum > 207) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							local K;
							local B;
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum > 209) then
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					else
						local K;
						local B;
						local A;
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Env[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Env[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return Stk[Inst[2]];
						end
					end
				elseif (Enum <= 316) then
					if (Enum <= 263) then
						if (Enum <= 236) then
							if (Enum <= 223) then
								if (Enum <= 216) then
									if (Enum <= 213) then
										if (Enum <= 211) then
											local A;
											local K;
											local B;
											Stk[Inst[2]] = Upvalues[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											do
												return Stk[A](Unpack(Stk, A + 1, Inst[3]));
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											do
												return Unpack(Stk, A, Top);
											end
											VIP = VIP + 1;
											Inst = Instr[VIP];
											do
												return;
											end
										elseif (Enum == 212) then
											local K;
											local B;
											local A;
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]][Inst[3]] = Inst[4];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Env[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A](Stk[A + 1]);
										else
											local A;
											local K;
											local B;
											Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Stk[Inst[3]];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											Stk[Inst[2]] = Inst[3];
											VIP = VIP + 1;
											Inst = Instr[VIP];
											B = Inst[3];
											K = Stk[B];
											for Idx = B + 1, Inst[4] do
												K = K .. Stk[Idx];
											end
											Stk[Inst[2]] = K;
											VIP = VIP + 1;
											Inst = Instr[VIP];
											A = Inst[2];
											Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
											VIP = VIP + 1;
											Inst = Instr[VIP];
											if not Stk[Inst[2]] then
												VIP = VIP + 1;
											else
												VIP = Inst[3];
											end
										end
									elseif (Enum <= 214) then
										local A = Inst[2];
										local T = Stk[A];
										local B = Inst[3];
										for Idx = 1, B do
											T[Idx] = Stk[A + Idx];
										end
									elseif (Enum > 215) then
										local A;
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									end
								elseif (Enum <= 219) then
									if (Enum <= 217) then
										local K;
										local B;
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return;
										end
									elseif (Enum == 218) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A]());
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									end
								elseif (Enum <= 221) then
									if (Enum > 220) then
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = {};
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A]();
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum > 222) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum <= 229) then
								if (Enum <= 226) then
									if (Enum <= 224) then
										local B;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
									elseif (Enum == 225) then
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Upvalues[Inst[3]];
									else
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Top));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
									end
								elseif (Enum <= 227) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								elseif (Enum == 228) then
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
								else
									local B;
									local T;
									local A;
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								end
							elseif (Enum <= 232) then
								if (Enum <= 230) then
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum == 231) then
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								else
									local A;
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								end
							elseif (Enum <= 234) then
								if (Enum > 233) then
									local A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum > 235) then
								local B;
								local A;
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Stk[Inst[2]] < Inst[4]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum <= 249) then
							if (Enum <= 242) then
								if (Enum <= 239) then
									if (Enum <= 237) then
										local T;
										local Edx;
										local Results, Limit;
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
										Top = (Limit + A) - 1;
										Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										T = Stk[A];
										for Idx = A + 1, Top do
											Insert(T, Stk[Idx]);
										end
									elseif (Enum > 238) then
										local K;
										local B;
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										B = Inst[3];
										K = Stk[B];
										for Idx = B + 1, Inst[4] do
											K = K .. Stk[Idx];
										end
										Stk[Inst[2]] = K;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									else
										local A;
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Stk[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
									end
								elseif (Enum <= 240) then
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum == 241) then
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
								end
							elseif (Enum <= 245) then
								if (Enum <= 243) then
									local K;
									local B;
									local A;
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
								elseif (Enum > 244) then
									local A = Inst[2];
									local Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							elseif (Enum <= 247) then
								if (Enum == 246) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								else
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								end
							elseif (Enum > 248) then
								local B;
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							end
						elseif (Enum <= 256) then
							if (Enum <= 252) then
								if (Enum <= 250) then
									Stk[Inst[2]] = Env[Inst[3]];
								elseif (Enum > 251) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								else
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								end
							elseif (Enum <= 254) then
								if (Enum > 253) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Stk[A](Unpack(Stk, A + 1, Inst[3]));
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									do
										return Unpack(Stk, A, Top);
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								end
							elseif (Enum > 255) then
								local A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
							else
								local B;
								local A;
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 259) then
							if (Enum <= 257) then
								local K;
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
							elseif (Enum > 258) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 261) then
							if (Enum == 260) then
								local A;
								Stk[Inst[2]]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Inst[3] ~= 0;
							end
						elseif (Enum == 262) then
							local A;
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local Edx;
							local Results, Limit;
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum <= 289) then
						if (Enum <= 276) then
							if (Enum <= 269) then
								if (Enum <= 266) then
									if (Enum <= 264) then
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Env[Inst[3]] = Stk[Inst[2]];
									elseif (Enum > 265) then
										local A = Inst[2];
										local Results, Limit = _R(Stk[A](Stk[A + 1]));
										Top = (Limit + A) - 1;
										local Edx = 0;
										for Idx = A, Top do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
									else
										local B;
										local A;
										Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										B = Stk[Inst[3]];
										Stk[A + 1] = B;
										Stk[A] = B[Inst[4]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										if Stk[Inst[2]] then
											VIP = VIP + 1;
										else
											VIP = Inst[3];
										end
									end
								elseif (Enum <= 267) then
									local K;
									local B;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum > 268) then
									local A = Inst[2];
									local Index = Stk[A];
									local Step = Stk[A + 2];
									if (Step > 0) then
										if (Index > Stk[A + 1]) then
											VIP = Inst[3];
										else
											Stk[A + 3] = Index;
										end
									elseif (Index < Stk[A + 1]) then
										VIP = Inst[3];
									else
										Stk[A + 3] = Index;
									end
								else
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Stk[Inst[3]] - Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
								end
							elseif (Enum <= 272) then
								if (Enum <= 270) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum > 271) then
									Stk[Inst[2]] = {};
								else
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 274) then
								if (Enum > 273) then
									local B;
									local A;
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local Edx;
									local Results;
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results = {Stk[A](Unpack(Stk, A + 1, Inst[3]))};
									Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								end
							elseif (Enum == 275) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							else
								local A = Inst[2];
								local C = Inst[4];
								local CB = A + 2;
								local Result = {Stk[A](Stk[A + 1], Stk[CB])};
								for Idx = 1, C do
									Stk[CB + Idx] = Result[Idx];
								end
								local R = Result[1];
								if R then
									Stk[CB] = R;
									VIP = Inst[3];
								else
									VIP = VIP + 1;
								end
							end
						elseif (Enum <= 282) then
							if (Enum <= 279) then
								if (Enum <= 277) then
									local T;
									local A;
									local K;
									local B;
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = {};
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									T = Stk[A];
									B = Inst[3];
									for Idx = 1, B do
										T[Idx] = Stk[A + Idx];
									end
								elseif (Enum > 278) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
								else
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 280) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Top));
							elseif (Enum == 281) then
								local A;
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 285) then
							if (Enum <= 283) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							elseif (Enum > 284) then
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							else
								local K;
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 287) then
							if (Enum > 286) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 288) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						else
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = #Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] % Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum <= 302) then
						if (Enum <= 295) then
							if (Enum <= 292) then
								if (Enum <= 290) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum > 291) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								else
									local K;
									local B;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 293) then
								local Results;
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							elseif (Enum > 294) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								local K;
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Upvalues[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return Stk[Inst[2]];
								end
							end
						elseif (Enum <= 298) then
							if (Enum <= 296) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 297) then
								local B;
								local A;
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local B;
								local A;
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum <= 300) then
							if (Enum == 299) then
								local Results;
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A]());
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results = {Stk[A](Unpack(Stk, A + 1, Top))};
								Edx = 0;
								for Idx = A, Inst[4] do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 301) then
							local B;
							local A;
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 309) then
						if (Enum <= 305) then
							if (Enum <= 303) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if not Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum > 304) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							end
						elseif (Enum <= 307) then
							if (Enum > 306) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local K;
								local B;
								local A;
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							end
						elseif (Enum > 308) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							local A = Inst[2];
							do
								return Unpack(Stk, A, Top);
							end
						end
					elseif (Enum <= 312) then
						if (Enum <= 310) then
							local B;
							local T;
							local A;
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							T = Stk[A];
							B = Inst[3];
							for Idx = 1, B do
								T[Idx] = Stk[A + Idx];
							end
						elseif (Enum == 311) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Env[Inst[3]] = Stk[Inst[2]];
						else
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						end
					elseif (Enum <= 314) then
						if (Enum > 313) then
							VIP = Inst[3];
						elseif (Inst[2] < Stk[Inst[4]]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					elseif (Enum == 315) then
						Stk[Inst[2]][Stk[Inst[3]]] = Stk[Inst[4]];
					else
						Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
					end
				elseif (Enum <= 369) then
					if (Enum <= 342) then
						if (Enum <= 329) then
							if (Enum <= 322) then
								if (Enum <= 319) then
									if (Enum <= 317) then
										local A;
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
									elseif (Enum == 318) then
										local A;
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Stk[A + 1]);
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Stk[A](Unpack(Stk, A + 1, Inst[3]));
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3] ~= 0;
										VIP = VIP + 1;
										Inst = Instr[VIP];
										do
											return Stk[Inst[2]];
										end
									else
										local Edx;
										local Results;
										local A;
										Env[Inst[3]] = Stk[Inst[2]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Inst[3];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										Stk[Inst[2]] = Env[Inst[3]];
										VIP = VIP + 1;
										Inst = Instr[VIP];
										A = Inst[2];
										Results = {Stk[A](Stk[A + 1])};
										Edx = 0;
										for Idx = A, Inst[4] do
											Edx = Edx + 1;
											Stk[Idx] = Results[Edx];
										end
										VIP = VIP + 1;
										Inst = Instr[VIP];
										VIP = Inst[3];
									end
								elseif (Enum <= 320) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								elseif (Enum == 321) then
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								else
									local B;
									local Edx;
									local Results, Limit;
									local A;
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								end
							elseif (Enum <= 325) then
								if (Enum <= 323) then
									local A;
									Env[Inst[3]] = Stk[Inst[2]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								elseif (Enum > 324) then
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									VIP = Inst[3];
								else
									local A = Inst[2];
									Stk[A](Stk[A + 1]);
								end
							elseif (Enum <= 327) then
								if (Enum == 326) then
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A]();
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									local A = Inst[2];
									local Results = {Stk[A](Stk[A + 1])};
									local Edx = 0;
									for Idx = A, Inst[4] do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
								end
							elseif (Enum > 328) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
							else
								local K;
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 335) then
							if (Enum <= 332) then
								if (Enum <= 330) then
									local Edx;
									local Results, Limit;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Results, Limit = _R(Stk[A](Stk[A + 1]));
									Top = (Limit + A) - 1;
									Edx = 0;
									for Idx = A, Top do
										Edx = Edx + 1;
										Stk[Idx] = Results[Edx];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
								elseif (Enum > 331) then
									local A;
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
								else
									local A;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Env[Inst[3]] = Stk[Inst[2]];
								end
							elseif (Enum <= 333) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							elseif (Enum == 334) then
								local B;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							else
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum <= 338) then
							if (Enum <= 336) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum == 337) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 340) then
							if (Enum > 339) then
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							else
								local A;
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum > 341) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						else
							local A;
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 355) then
						if (Enum <= 348) then
							if (Enum <= 345) then
								if (Enum <= 343) then
									local K;
									local B;
									local A;
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3] ~= 0;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return Stk[Inst[2]];
									end
									VIP = VIP + 1;
									Inst = Instr[VIP];
									do
										return;
									end
								elseif (Enum > 344) then
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Stk[Inst[3]] % Inst[4];
								end
							elseif (Enum <= 346) then
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 347) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] <= Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 351) then
							if (Enum <= 349) then
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum == 350) then
								local A;
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							end
						elseif (Enum <= 353) then
							if (Enum == 352) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Top)));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Inst[2] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 354) then
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3] ~= 0;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return Stk[Inst[2]];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 362) then
						if (Enum <= 358) then
							if (Enum <= 356) then
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							elseif (Enum > 357) then
								local B;
								local T;
								local A;
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								T = Stk[A];
								B = Inst[3];
								for Idx = 1, B do
									T[Idx] = Stk[A + Idx];
								end
							else
								local B;
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								B = Stk[Inst[3]];
								Stk[A + 1] = B;
								Stk[A] = B[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Env[Inst[3]] = Stk[Inst[2]];
							end
						elseif (Enum <= 360) then
							if (Enum == 359) then
								local K;
								local B;
								local A;
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] == Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							end
						elseif (Enum > 361) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
						end
					elseif (Enum <= 365) then
						if (Enum <= 363) then
							if (Inst[2] <= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						elseif (Enum > 364) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
						else
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Unpack(Stk, A + 1, Inst[3])));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
						end
					elseif (Enum <= 367) then
						if (Enum == 366) then
							local K;
							local B;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local B = Inst[3];
							local K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
						end
					elseif (Enum > 368) then
						Stk[Inst[2]] = Inst[3];
					else
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 395) then
					if (Enum <= 382) then
						if (Enum <= 375) then
							if (Enum <= 372) then
								if (Enum <= 370) then
									local K;
									local B;
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									B = Inst[3];
									K = Stk[B];
									for Idx = B + 1, Inst[4] do
										K = K .. Stk[Idx];
									end
									Stk[Inst[2]] = K;
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if not Stk[Inst[2]] then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								elseif (Enum == 371) then
									local B;
									local A;
									Stk[Inst[2]][Inst[3]] = Inst[4];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									B = Stk[Inst[3]];
									Stk[A + 1] = B;
									Stk[A] = B[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Env[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									A = Inst[2];
									Stk[A](Stk[A + 1]);
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									if (Stk[Inst[2]] == Inst[4]) then
										VIP = VIP + 1;
									else
										VIP = Inst[3];
									end
								else
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Upvalues[Inst[3]];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
									VIP = VIP + 1;
									Inst = Instr[VIP];
									Stk[Inst[2]] = Inst[3];
								end
							elseif (Enum <= 373) then
								local A;
								local K;
								local B;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
							elseif (Enum > 374) then
								local A;
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Stk[Inst[4]]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							else
								local A;
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								VIP = Inst[3];
							end
						elseif (Enum <= 378) then
							if (Enum <= 376) then
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A]();
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
							elseif (Enum > 377) then
								local Edx;
								local Results, Limit;
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Results, Limit = _R(Stk[A](Stk[A + 1]));
								Top = (Limit + A) - 1;
								Edx = 0;
								for Idx = A, Top do
									Edx = Edx + 1;
									Stk[Idx] = Results[Edx];
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Upvalues[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								if (Stk[Inst[2]] < Stk[Inst[4]]) then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							else
								Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							end
						elseif (Enum <= 380) then
							if (Enum > 379) then
								Stk[Inst[2]] = {};
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							else
								local K;
								local B;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
							end
						elseif (Enum > 381) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						end
					elseif (Enum <= 388) then
						if (Enum <= 385) then
							if (Enum <= 383) then
								Stk[Inst[2]] = #Stk[Inst[3]];
							elseif (Enum == 384) then
								local A;
								local K;
								local B;
								B = Inst[3];
								K = Stk[B];
								for Idx = B + 1, Inst[4] do
									K = K .. Stk[Idx];
								end
								Stk[Inst[2]] = K;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							else
								local A;
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Stk[A](Unpack(Stk, A + 1, Inst[3]));
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								do
									return Unpack(Stk, A, Top);
								end
								VIP = VIP + 1;
								Inst = Instr[VIP];
								do
									return;
								end
							end
						elseif (Enum <= 386) then
							for Idx = Inst[2], Inst[3] do
								Stk[Idx] = nil;
							end
						elseif (Enum == 387) then
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 391) then
						if (Enum <= 389) then
							local K;
							local B;
							local A;
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						elseif (Enum == 390) then
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] < Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 393) then
						if (Enum == 392) then
							Stk[Inst[2]] = not Stk[Inst[3]];
						else
							local NewProto = Proto[Inst[3]];
							local NewUvals;
							local Indexes = {};
							NewUvals = Setmetatable({}, {__index=function(_, Key)
								local Val = Indexes[Key];
								return Val[1][Val[2]];
							end,__newindex=function(_, Key, Value)
								local Val = Indexes[Key];
								Val[1][Val[2]] = Value;
							end});
							for Idx = 1, Inst[4] do
								VIP = VIP + 1;
								local Mvm = Instr[VIP];
								if (Mvm[1] == 88) then
									Indexes[Idx - 1] = {Stk,Mvm[3]};
								else
									Indexes[Idx - 1] = {Upvalues,Mvm[3]};
								end
								Lupvals[#Lupvals + 1] = Indexes;
							end
							Stk[Inst[2]] = Wrap(NewProto, NewUvals, Env);
						end
					elseif (Enum > 394) then
						Stk[Inst[2]] = {};
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]][Inst[3]] = Inst[4];
					else
						local B;
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						B = Stk[Inst[3]];
						Stk[A + 1] = B;
						Stk[A] = B[Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if Stk[Inst[2]] then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					end
				elseif (Enum <= 408) then
					if (Enum <= 401) then
						if (Enum <= 398) then
							if (Enum <= 396) then
								if Stk[Inst[2]] then
									VIP = VIP + 1;
								else
									VIP = Inst[3];
								end
							elseif (Enum == 397) then
								local A;
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A] = Stk[A](Stk[A + 1]);
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Stk[Inst[3]] * Stk[Inst[4]];
							else
								local A;
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3] ~= 0;
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Unpack(Stk, A + 1, Inst[3]));
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Env[Inst[3]];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								Stk[Inst[2]] = Inst[3];
								VIP = VIP + 1;
								Inst = Instr[VIP];
								A = Inst[2];
								Stk[A](Stk[A + 1]);
							end
						elseif (Enum <= 399) then
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
						elseif (Enum == 400) then
							local B;
							local A;
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							B = Stk[Inst[3]];
							Stk[A + 1] = B;
							Stk[A] = B[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] + Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if (Stk[Inst[2]] ~= Stk[Inst[4]]) then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						end
					elseif (Enum <= 404) then
						if (Enum <= 402) then
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							VIP = Inst[3];
						elseif (Enum == 403) then
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A]();
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] / Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]] - Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = {};
						end
					elseif (Enum <= 406) then
						if (Enum > 405) then
							local A = Inst[2];
							Stk[A] = Stk[A]();
						else
							local Edx;
							local Results, Limit;
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Env[Inst[3]] = Stk[Inst[2]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Results, Limit = _R(Stk[A](Stk[A + 1]));
							Top = (Limit + A) - 1;
							Edx = 0;
							for Idx = A, Top do
								Edx = Edx + 1;
								Stk[Idx] = Results[Edx];
							end
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Top));
						end
					elseif (Enum == 407) then
						local A;
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return Stk[Inst[2]];
						end
					else
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Env[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Env[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
					end
				elseif (Enum <= 415) then
					if (Enum <= 411) then
						if (Enum <= 409) then
							local A = Inst[2];
							local T = Stk[A];
							for Idx = A + 1, Inst[3] do
								Insert(T, Stk[Idx]);
							end
						elseif (Enum == 410) then
							local A;
							local K;
							local B;
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Inst[4];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Stk[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						else
							local A;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Unpack(Stk, A + 1, Inst[3]));
						end
					elseif (Enum <= 413) then
						if (Enum == 412) then
							local A;
							local K;
							local B;
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Upvalues[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							B = Inst[3];
							K = Stk[B];
							for Idx = B + 1, Inst[4] do
								K = K .. Stk[Idx];
							end
							Stk[Inst[2]] = K;
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A] = Stk[A](Unpack(Stk, A + 1, Inst[3]));
							VIP = VIP + 1;
							Inst = Instr[VIP];
							if not Stk[Inst[2]] then
								VIP = VIP + 1;
							else
								VIP = Inst[3];
							end
						else
							local A;
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Env[Inst[3]];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							Stk[Inst[2]] = Inst[3];
							VIP = VIP + 1;
							Inst = Instr[VIP];
							A = Inst[2];
							Stk[A](Stk[A + 1]);
							VIP = VIP + 1;
							Inst = Instr[VIP];
							do
								return;
							end
						end
					elseif (Enum > 414) then
						local A;
						local K;
						local B;
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Env[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						if (Stk[Inst[2]] == Inst[4]) then
							VIP = VIP + 1;
						else
							VIP = Inst[3];
						end
					else
						local A;
						local K;
						local B;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
					end
				elseif (Enum <= 418) then
					if (Enum <= 416) then
						local Results;
						local Edx;
						local Results, Limit;
						local A;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results, Limit = _R(Stk[A]());
						Top = (Limit + A) - 1;
						Edx = 0;
						for Idx = A, Top do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Results = {Stk[A](Unpack(Stk, A + 1, Top))};
						Edx = 0;
						for Idx = A, Inst[4] do
							Edx = Edx + 1;
							Stk[Idx] = Results[Edx];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					elseif (Enum > 417) then
						local K;
						local B;
						local A;
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A] = Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Upvalues[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Env[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return;
						end
					else
						local A;
						Env[Inst[3]] = Stk[Inst[2]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3] ~= 0;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						do
							return Stk[Inst[2]];
						end
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum <= 420) then
					if (Enum == 419) then
						local A;
						local K;
						local B;
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Inst[3];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						B = Inst[3];
						K = Stk[B];
						for Idx = B + 1, Inst[4] do
							K = K .. Stk[Idx];
						end
						Stk[Inst[2]] = K;
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Stk[A + 1]);
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
					else
						local A;
						Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Env[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						Stk[Inst[2]] = Stk[Inst[3]];
						VIP = VIP + 1;
						Inst = Instr[VIP];
						A = Inst[2];
						Stk[A](Unpack(Stk, A + 1, Inst[3]));
						VIP = VIP + 1;
						Inst = Instr[VIP];
						VIP = Inst[3];
					end
				elseif (Enum > 421) then
					local A;
					A = Inst[2];
					Stk[A] = Stk[A](Stk[A + 1]);
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]][Inst[3]] = Stk[Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					A = Inst[2];
					Stk[A](Unpack(Stk, A + 1, Inst[3]));
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Stk[Inst[3]][Inst[4]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
				else
					Stk[Inst[2]] = Stk[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Env[Inst[3]];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
					VIP = VIP + 1;
					Inst = Instr[VIP];
					Stk[Inst[2]] = Inst[3];
				end
				VIP = VIP + 1;
			end
		end;
	end
	return Wrap(Deserialize(), {}, vmenv)(...);
end
return VMCall("LOL!54012Q0003093Q006B65796469616C6F6703023Q006F7303073Q006361707475726503073Q006F7665726D73672Q033Q006C6F67030D3Q004F6E546578744F7665726C6179030B3Q0076616C69646174654B657903083Q00636F6C6F72732Q7803053Q00626C61636B03053Q001B5B33306D2Q033Q0072656403053Q001B5B33316D03053Q0067722Q656E03053Q001B5B33326D03063Q0079652Q6C6F7703053Q001B5B2Q336D03043Q00626C756503053Q001B5B33346D03073Q006D6167656E746103053Q001B5B33356D03043Q006379616E03053Q001B5B33366D03053Q00776869746503053Q001B5B33376D03053Q00726573657403043Q001B5B306D03103Q007072696E74436F6C6F72656454657874030A3Q00436865636B4C6F636B7303143Q0073686F77436F2Q6C6563746564456E61626C656403043Q006E616D65030E3Q00426C61636B2047656D204C6F636B03053Q00636F6C6F7203023Q006062030C3Q004469616D6F6E64204C6F636B03023Q006021030A3Q00576F726C64204C6F636B03023Q006039030D3Q00426C75652047656D204C6F636B03023Q00606503133Q006C6F67436F2Q6C65637465644D652Q73616765028Q00025Q00408F4003163Q0073656E64436F6C6F7265644C6F636B4D652Q73616765030B3Q00436865636B4C6F636B2Q7303053Q0072656C6F67030C3Q0072656D6F762Q652Q66656374030D3Q0064657465636B7265737061776E03023Q00647003023Q00776403063Q006E692Q676172030C3Q00636865636B5F574F524C443203073Q007574696C69747903063Q00434C4F564552025Q002Q804003023Q00574C025Q00406E4003023Q00444C025Q00109C402Q033Q0042474C025Q0014BC4003053Q004952454E47025Q008FC640030B3Q007961746175746175616A6103083Q00626C6F636B736462030B3Q0074656C657761726E696E67030D3Q00626C6F636B736B696E7761726E030E3Q00626C6F636B736B696E7761726E32030D3Q0074656C657761726E696E672Q3103103Q00626C756567656D6C6F636B6E6F746966030E3Q00556E6B6E6F776E636F2Q6D616E64030D3Q006661732Q74656C6570686F6E65030F3Q00736F6D657468696E67696C6567616C03043Q0074656C6503073Q00736B696E6C6F6C03083Q00746F2Q676C65465403063Q0066747261736803023Q00666403073Q0064726F70506F7303053Q006664726F7003073Q004C6F675370696E034Q0003073Q004C6F6744726F70030A3Q004C6F67436F2Q6C65637403063Q004C6F6742455403063Q004C6F6757494E03073Q006C6F676D656E7503023Q006C7303023Q006C6403023Q006C6303043Q0062742Q6B03053Q0062742Q6B3103053Q00682Q6F6B3303063Q006474315F786403023Q00617003023Q00616B03023Q00616203093Q007370616D746578747303083Q00603447412Q532Q21030E3Q0070752Q6C42414E4B49434B6C6F6C03043Q0044726F7003073Q007465787465746303143Q0060775B606320576176652050726F78792060775D030A3Q0064726F70637573746F6D030B3Q0070726F63652Q7344726F7003083Q0064726F704974656D030D3Q0064726F70576F726C644C6F636B030F3Q0064726F704469616D6F6E644C6F636B030F3Q0064726F70426C756547656D4C6F636B03103Q0064726F70426C61636B47656D4C6F636B03023Q00723203023Q00723403023Q00696403013Q003903073Q00636F2Q6D616E6403023Q00647703013Q006303023Q002Q6403013Q006503023Q00646203013Q00622Q033Q00642Q62030D3Q0064726F7053706C69744C6F636B2Q033Q0064617703073Q00436F6E736F6C65030A3Q0073686F77652Q66656374026Q00F03F030E3Q00416374697661746562746B6C6F67030F3Q00416374697661746566616B656C6F6703073Q0057692Q6E65723103063Q004368616E643103123Q0041637469766174657061746866696E64657203133Q004163746976617761726E696E676F6E6A6F696E03143Q004163746976617761726E696E676F6E6A6F696E32030D3Q00416374697661636F6E76657274030A3Q004163746976616661737403063Q00652Q6665637403073Q00776562682Q6F6B03073Q0066616B656C6F6703073Q007761726E696E6703083Q007761726E696E673203053Q006175746F6303043Q0066617374030B3Q00416374697661636F6C656B030A3Q004163746976616E616D65030E3Q004163746976617370692Q6E616D6503133Q00416374697661746567656D73636865636B6572030D3Q00616374697661636F6E736F6C6503063Q007370616D6C77030C3Q006163746976617370616D6C7703073Q007370696E616D6503103Q0041637469766174656175746F62616E3103103Q0041637469766174656175746F62616E3203103Q0041637469766174656175746F62616E3303103Q0041637469766174656175746F62616E3403103Q0041637469766174656175746F62616E3503103Q0041637469766174656175746F62616E3603153Q0041637469766174656175746F62616E66696E616C6503113Q00646973706C617942544B4F7074696F6E73030F3Q0068616E646C6542544B436F6E6669672Q033Q0063666703133Q0063726561746544656661756C74436F6E666967030A3Q0073617665436F6E666967030A3Q006C6F6164436F6E666967030B3Q00636667736176656C6F616403133Q00646973706C6179436F6E66696753746174757303093Q0063666773746174757303063Q007475726E2Q7303093Q00656D6F7469636F6E7303063Q00286E756B652903053Q00287368792903053Q00286D61642903053Q00286C6F6C2903053Q00286372792903063Q00286C6F76652903073Q002870656163652903063Q00282Q6F70732903073Q0028736D696C652903073Q002870617274792903073Q002862752Q6E792903063Q002868616C6F2903083Q0028746F6E6775652903063Q0028657965732903073Q0028706C6561642903073Q002877656172792903073Q002867686F73742903043Q00286E6F2903053Q00287965732903063Q0028636C61702903073Q00286167722Q652903073Q002870756E63682903083Q00286268656172742903063Q002870696E652903063Q002877696E6B2903063Q00286576696C2903063Q0028736F6E672903063Q002867656D7329030D3Q0028732Q652D6E6F2D6576696C2903063Q002867726F772903083Q00287475726B65792903073Q00286D757369632903053Q0028776F772903093Q007370616D64656C6179025Q0088B34003093Q0073746172747370616D03113Q007370616D77697468656D6F7469636F6E7303113Q007370616D77697468656D6F7469636F6E3103053Q007370616D3203083Q005370616D5465787403203Q0057484F204741532042474C202D20414D50452053454D455354412028776F772903143Q00646973706C61795370616D5365744469616C6F6703193Q0068616E646C655365745370616D54657874416E6444656C6179030C3Q0073656E64456D6F7469636F6E03073Q007365747370616D03043Q007370616D026Q00344003153Q004155544F20534220425920574156452050524F585903103Q00606323574156452050524F5859205342026Q000840026Q001C4003143Q0063726561746544656661756C74436F6E6669673103133Q007361766542726F616463617374436F6E66696703133Q006C6F616442726F616463617374436F6E66696703063Q0073757065726203093Q00736574436F6E66696703143Q00646973706C6179436F6E6669675374617475733103073Q007365746361737403083Q0073746F7063617374030D3Q00737461727462726F6463617374030C3Q0073657462726F61646361737403043Q007369676E03073Q00482Q6F6B322Q3003013Q003403043Q006461746503053Q0025483A254D03063Q006469616C6F6703083Q0070726F787964756803023Q00637603063Q00434F4C4F525303023Q00603003023Q00603103023Q00603203023Q00603303023Q00603403023Q00603503023Q00603603023Q00603703023Q00603803023Q00606103023Q00606303023Q00606403023Q00606603023Q00607203023Q00602403023Q00607303023Q00602603023Q00605E03023Q00607703093Q00454D4F5449434F4E5303053Q007475726E7303133Q00636F6C6F7266756C54657874456E61626C656403143Q0067656E6572617465436F6C6F7266756C5465787403103Q00656D6F6A6963686174636F2Q6D616E6403193Q00746F2Q676C65636F6C6F7266756C54657874456E61626C656403053Q0074656C657803053Q0074656C6579026Q00F0BF03053Q0074696C657303063Q0074696C65733203093Q00636F2Q6C6563742Q6403023Q00747803023Q0074792Q033Q007731782Q033Q007731792Q033Q007732782Q033Q007732792Q033Q00746178026Q0014402Q033Q0077696E03023Q00736C03043Q006D6F766503083Q00636F2Q6C6563743203073Q00636F2Q6C656374030D3Q006E6574696466726F6D6E616D6503013Q006C03093Q00636F756E7464726F70030A3Q00636F756E7464726F703203053Q007361762Q6503053Q006C6F612Q6403083Q004661636553696465030F3Q0068616E646C655761766550726F787903083Q0068616E646C65573103083Q0068616E646C655732030C3Q0068616E646C65546178506F73030C3Q0068616E646C6553657454617803073Q00682Q6F6B62746B03073Q00412Q64482Q6F6B03083Q004F6E5061636B657403093Q007862746B636865636B03063Q0073657467656D03163Q0068616E646C655761766550726F7879416374696F6E7303133Q0073656E645061727469636C65452Q6665637431031C3Q006372656174654C617267655061727469636C65426F78452Q6665637403173Q006372656174655061727469636C65426F78452Q6665637403043Q002Q42474C03063Q00737472696E67030C3Q0072656D6F7665436F6C6F727303063Q0062746B776562030A3Q0068616E646C654265747303023Q00747003023Q00617703023Q00636703043Q007374617403023Q006370030F3Q00636865636B67656D73726573756C74030B3Q00636F2Q6C65637467656D7303073Q00612Q6C67656D7303023Q006361030B3Q0072656D655F6B6F6E746F6C030B3Q002Q715F66756E6374696F6E030D3Q0072656D655F66756E6374696F6E030D3Q006E616D6566726F6D6E6574696403083Q0066696E644E616D6503073Q0066696E6475696403083Q00612Q6C5F7370696E03053Q00536C2Q6570026Q00494003083Q004F6E4E692Q67657203073Q002Q715F7370696E03103Q004F6E4F6B616B64616F646B61736F646B030D3Q0072656D6571656D655F7370696E03053Q0072716D653103093Q0072656D655F7370696E03103Q004F6E5061646D616B646D61696A736E64030C3Q005370696E5F636865636B657203093Q004F6E5661726C69737403183Q004F61646B616964616A7564756138686475383Q61646164030A3Q00636865636B5F7370696E031F3Q004F6E5061636B6574616461736461736461736461642Q617364616461647364030F3Q0068616E646C654B657953797374656D030B3Q0076616C69646174657569640004032Q00029C7Q00120A3Q00013Q0012FA3Q00023Q00029C000100013Q00101D012Q0003000100029C3Q00023Q00120A3Q00043Q00029C3Q00033Q00120A3Q00053Q00029C3Q00043Q00120A3Q00063Q00029C3Q00053Q00120A3Q00074Q008B014Q000900304Q0009000A00304Q000B000C00304Q000D000E00304Q000F001000304Q0011001200304Q0013001400304Q0015001600304Q0017001800304Q0019001A00120A3Q00083Q00029C3Q00063Q00120A3Q001B3Q00029C3Q00073Q00120A3Q001C4Q0010017Q00822Q0100014Q0005010200013Q00120A0002001D4Q0010010200044Q001001033Q000200302B0003001E001F00302B0003002000212Q001001043Q000200302B0004001E002200302B0004002000232Q001001053Q000200302B0005001E002400302B0005002000252Q001001063Q000200302B0006001E002600302B0006002000272Q00D600020004000100029C000300083Q00120A000300283Q001271010300293Q0012710104002A3Q00068901050009000100042Q00583Q00034Q00583Q00044Q00583Q00024Q00587Q00120A0005002B3Q0006890105000A000100032Q00583Q00024Q00588Q00583Q00013Q00120A0005002C3Q00029C0005000B3Q00120A0005002D3Q00029C0005000C3Q00120A0005002E3Q00029C0005000D3Q00120A0005002F3Q00029C0005000E3Q00029C0006000F3Q00029C000700103Q00068901080011000100022Q00583Q00054Q00583Q00063Q00120A000800303Q00068901080012000100012Q00583Q00073Q00120A000800313Q00029C000800133Q00120A000800323Q00029C000800143Q00120A000800333Q00029C000800153Q00029C000900163Q000689010A0017000100022Q00583Q00094Q00583Q00083Q00120A000A00344Q0010010A3Q000500302B000A0035003600302B000A0037003800302B000A0039003A00302B000A003B003C00302B000A003D003E00029C000B00183Q000689010C0019000100012Q00583Q000B3Q000689010D001A000100022Q00583Q000C4Q00583Q000A3Q00120A000D003F3Q00029C000D001B3Q00120A000D00403Q00029C000D001C3Q00120A000D00413Q00029C000D001D3Q00120A000D00423Q00029C000D001E3Q00120A000D00433Q00029C000D001F3Q00120A000D00443Q00029C000D00203Q00120A000D00453Q00029C000D00213Q00120A000D00463Q00029C000D00223Q00120A000D00473Q00029C000D00233Q00120A000D00483Q00029C000D00243Q00120A000D00493Q00029C000D00253Q00120A000D004A4Q0005010D5Q001271010E00293Q001271010F00294Q000501105Q00068901110026000100032Q00583Q000D4Q00583Q000E4Q00583Q000F3Q00068901120027000100022Q00583Q00104Q00583Q000D3Q00120A0012004B3Q00029C001200283Q00120A0012004C4Q000501125Q00120A0012004D3Q001271011200293Q00120A0012004E3Q001271010F00293Q00068901120029000100012Q00583Q000F3Q00029C0013002A3Q0006890114002B000100012Q00583Q00133Q0012B20014004F3Q00122Q001400513Q00122Q001400503Q00122Q001400513Q00122Q001400523Q00122Q001400513Q00122Q001400533Q00122Q001400513Q00122Q001400543Q00122Q001400513Q00120A001400553Q00029C0014002C3Q00120A001400563Q00029C0014002D3Q00120A001400573Q00029C0014002E3Q00120A001400583Q00029C0014002F3Q00120A001400593Q00029C001400303Q00120A0014005A3Q00029C001400313Q00120A0014005B3Q00029C001400323Q00120A0014005C3Q00029C001400333Q00120A0014005D4Q000501145Q00120A0014005E4Q000501145Q00120A0014005F4Q000501145Q00120A001400603Q001271011400623Q00120A001400613Q00029C001400343Q00029C001500353Q00120A001500633Q00029C001500363Q00120A001500643Q001271011500663Q00120A001500653Q00029C001500373Q00120A001500673Q00029C001500383Q00120A001500683Q00029C001500393Q00120A001500693Q00029C0015003A3Q00120A0015006A3Q00029C0015003B3Q00120A0015006B3Q00029C0015003C3Q00120A0015006C3Q00029C0015003D3Q00120A0015006D3Q00029C0015003E3Q00120A0015006E3Q00029C0015003F3Q00120A0015006F4Q0010011500044Q001001163Q000400302B0016001E002400302B00160070003800302B00160020007100302B0016007200732Q001001173Q000400302B0017001E002200302B00170070003A00302B00170020007400302B0017007200752Q001001183Q000400302B0018001E002600302B00180070003C00302B00180020007600302B0018007200772Q001001193Q000400302B0019001E001F00302B00190070003E00302B00190020007800302B0019007200792Q00D600150004000100029C001600403Q00068901170041000100012Q00583Q00163Q00029C001800423Q00120A0018007A3Q00029C001800433Q00120A0018007B3Q00029C001800443Q0012B20018007C3Q00122Q0018007E3Q00122Q0018007D3Q00122Q0018007E3Q00122Q0018007F3Q00122Q0018007E3Q00122Q001800803Q00122Q0018007E3Q00122Q001800813Q00122Q0018007E3Q0012B2001800823Q00122Q0018007E3Q00122Q001800833Q00122Q0018007E3Q00122Q001800843Q00122Q0018007E3Q00122Q001800853Q00122Q0018007E3Q00122Q001800863Q00122Q0018007E3Q00120A001800874Q0005011800013Q00120A001800884Q0005011800013Q00120A001800894Q0005011800013Q00120A0018008A4Q0005011800013Q00120A0018008B4Q0005011800013Q00120A0018008C4Q0005011800013Q00120A0018008D4Q0005011800013Q0012B20018008E3Q00122Q0018007E3Q00122Q0018008F3Q00122Q001800293Q00122Q001800903Q00122Q0018007E3Q00122Q001800913Q00122Q0018007E3Q00122Q001800923Q00122Q001800293Q00120A001800934Q000501185Q00120A001800943Q001271011800293Q00120A001800954Q0005011800013Q0012B2001800963Q00122Q001800293Q00122Q001800973Q00122Q001800293Q00122Q001800983Q00122Q001800293Q00122Q001800993Q00122Q001800293Q00122Q0018009A3Q00122Q001800293Q00120A0018009B3Q001271011800293Q00120A0018009C3Q001271011800293Q00120A0018009D3Q00029C001800453Q00120A0018009E3Q00029C001800463Q00120A0018009F3Q00029C001800473Q00120A001800A03Q00029C001800483Q00120A001800A13Q00029C001800493Q00120A001800A23Q00029C0018004A3Q00120A001800A33Q00029C0018004B3Q00120A001800A43Q00029C0018004C3Q00120A001800A53Q00029C0018004D3Q00120A001800A63Q001271011800293Q0012DD001800A76Q001800193Q00122Q001900A93Q00122Q001A00AA3Q00122Q001B00AB3Q00122Q001C00AC3Q00122Q001D00AD3Q00122Q001E00AE3Q00122Q001F00AF3Q00122Q002000B03Q001264002100B13Q00122Q002200B23Q00122Q002300B33Q00122Q002400B43Q00122Q002500B53Q00122Q002600B63Q00122Q002700B73Q00122Q002800B83Q00122Q002900B93Q00122Q002A00BA3Q001271012B00BB3Q001271012C00BC3Q001271012D00BD3Q001271012E00BE3Q001271012F00BF3Q001271013000C03Q001271013100C13Q00123B003200C23Q00122Q003300C33Q00122Q003400BC3Q00122Q003500C43Q00122Q003600C53Q00122Q003700B23Q00122Q003800C63Q00122Q003900C73Q00122Q003A00C83Q00122Q003B00C96Q00180023000100120A001800A83Q001271011800CB3Q00120A001800CA3Q001271011800293Q00120A001800CC3Q001271011800293Q00120A001800CD4Q000501185Q00120A001800CE4Q000501185Q00120A001800CF3Q001271011800D13Q00120A001800D03Q00029C0018004E3Q00120A001800D23Q00029C0018004F3Q00120A001800D33Q00029C001800503Q00120A001800D43Q00029C001800513Q00120A001800D53Q00029C001800523Q00126A001800D63Q00122Q001800293Q00122Q001900D73Q00122Q001A00D83Q00122Q001B00D93Q00122Q001C00DA3Q00122Q001D00DB3Q00029C001E00533Q00120A001E00DC3Q000689011E0054000100062Q00583Q00184Q00583Q00194Q00583Q001C4Q00583Q001D4Q00583Q001A4Q00583Q001B3Q00120A001E00DD3Q000689011E0055000100062Q00583Q00184Q00583Q00194Q00583Q001C4Q00583Q001D4Q00583Q001A4Q00583Q001B3Q00120A001E00DE3Q000689011E0056000100062Q00583Q00184Q00583Q00194Q00583Q001C4Q00583Q001D4Q00583Q001A4Q00583Q001B3Q00120A001E00DF3Q000689011E0057000100062Q00583Q00184Q00583Q00194Q00583Q001C4Q00583Q001D4Q00583Q001A4Q00583Q001B3Q00120A001E00E03Q000689011E0058000100062Q00583Q00184Q00583Q00194Q00583Q001C4Q00583Q001D4Q00583Q001A4Q00583Q001B3Q00120A001E00E13Q00029C001E00593Q00120A001E00E24Q0005011E5Q000689011F005A000100012Q00583Q001E3Q0006890120005B000100012Q00583Q001F3Q00120A002000E33Q0006890120005C000100062Q00583Q00184Q00583Q00194Q00583Q001C4Q00583Q001D4Q00583Q001A4Q00583Q001B3Q0006890121005D000100082Q00583Q001E4Q00583Q001D4Q00583Q00184Q00583Q00194Q00583Q001A4Q00583Q001B4Q00583Q00204Q00583Q001C3Q00120A002100E43Q00029C0021005E3Q00120A002100E54Q000501215Q00120A002100E63Q0006890121005F000100012Q00583Q001A3Q001206002100E73Q00122Q002100E83Q00122Q002200023Q00202Q0022002200E900122Q002300EA6Q00220002000200068901230060000100012Q00583Q00223Q00120A002300EB3Q00029C002300613Q00120A002300EC3Q00029C002300623Q0012DD002300ED6Q002300133Q00122Q002400EF3Q00122Q002500F03Q00122Q002600F13Q00122Q002700F23Q00122Q002800F33Q00122Q002900F43Q00122Q002A00F53Q00122Q002B00F63Q001271012C00F73Q001271012D00253Q001271012E00F83Q001271012F00213Q00123B003000F93Q00122Q003100FA3Q00122Q003200273Q00122Q003300FB3Q00122Q003400FC3Q00122Q003500FD3Q00122Q003600FE3Q00122Q003700FF3Q00122Q00382Q00012Q00122Q0039002Q015Q00230016000100120A002300EE4Q0071002300193Q00122Q002400A93Q00122Q002500AA3Q00122Q002600AB3Q00122Q002700AC3Q00122Q002800AD3Q00122Q002900AE3Q00122Q002A00AF3Q00122Q002B00B03Q00122Q002C00B13Q001264002D00B23Q00122Q002E00B33Q00122Q002F00B43Q00122Q003000B53Q00122Q003100B63Q00122Q003200B73Q00122Q003300B83Q00122Q003400B93Q00122Q003500BA3Q00122Q003600BB3Q001271013700BC3Q001271013800BD3Q001271013900BE3Q001271013A00BF3Q001271013B00C03Q001271013C00C13Q00123B003D00C23Q00122Q003E00C33Q00122Q003F00BC3Q00122Q004000C43Q00122Q004100C53Q00122Q004200B23Q00122Q004300C63Q00122Q004400C73Q00122Q004500C83Q00122Q004600C96Q00230023000100120A00230002012Q001271012300293Q00120A00230003013Q0005012300013Q00120A00230004012Q00029C002300633Q00120A00230005013Q000501235Q00068901240064000100012Q00583Q00233Q00120A00240006012Q00029C002400653Q00120A00240007012Q0012710124000A012Q0012710125000A012Q00120A00250009012Q00120A00240008013Q001001245Q00120A0024000B013Q001001245Q00120A0024000C013Q001001245Q00120A0024000D012Q001271012400293Q001271012500293Q00120A0025000F012Q00120A0024000E012Q001271012400293Q001271012500293Q00120A00250011012Q00120A00240010012Q001271012400293Q001271012500293Q00120A00250013012Q00120A00240012012Q00127101240015012Q00120A00240014012Q001271012400293Q00120A00240016012Q00029C002400663Q00120A00240017012Q00029C002400673Q00120A00240018012Q00029C002400683Q00029C002500693Q00120A00250019012Q00029C0025006A3Q00120A0025001A012Q00029C0025006B3Q00120A0025001B012Q00029C0025006C3Q00120A0025001C012Q00029C0025006D3Q00120A0025001D012Q00029C0025006E3Q00120A0025001E012Q00029C0025006F3Q00120A0025001F012Q00029C002500703Q00120A00250020012Q00029C002500713Q00120A00250021012Q00029C002500723Q00120A00250022012Q00029C002500733Q00120A00250023012Q00029C002500743Q00120A00250024012Q00029C002500753Q00120A00250025012Q00029C002500763Q00120A00250026012Q00029C002500773Q00120400250027012Q00122Q00250028012Q00122Q00260029012Q00122Q0027002A012Q00122Q00280027015Q00250028000100029C002500783Q00120A0025002B012Q00029C002500793Q00120A0025002C012Q00029C0025007A3Q00029C0026007B3Q00120A0026002D012Q00029C0026007C3Q00120A0026002E012Q00029C0026007D3Q0012E60026002F015Q00263Q000400122Q002700383Q00102Q00260037002700122Q0027003A3Q00102Q00260039002700122Q0027003C3Q00102Q0026003B002700122Q00270030012Q00122Q0028003E4Q003B01260027002800029C0027007E3Q00029C0028007F3Q00029C002900803Q0012FA002A0031012Q001271012B0032012Q00029C002C00814Q003B012A002B002C000689012A0082000100012Q00583Q00223Q00120A002A0033012Q000689012A0083000100052Q00583Q00254Q00583Q00264Q00583Q00274Q00583Q00284Q00583Q00293Q00120A002A0034012Q00029C002A00843Q00120A002A0035012Q00029C002A00853Q00029C002B00863Q000689012C0087000100012Q00583Q002A3Q00120A002C0036012Q00029C002C00883Q00120A002C0037012Q00029C002C00893Q00120A002C0038012Q000689012C008A000100022Q00583Q002B4Q00583Q00243Q00120A002C0039012Q00029C002C008B3Q00120A002C003A012Q00029C002C008C3Q00120A002C003B012Q000689012C008D000100022Q00583Q002B4Q00583Q00243Q00120A002C003C012Q00029C002C008E3Q00120A002C003D012Q0012FA002C0031012Q001271012D0032012Q00029C002E008F4Q003B012C002D002E00029C002C00903Q00120A002C003E012Q00029C002C00913Q00120A002C003F012Q00029C002C00923Q00120A002C0040012Q00029C002C00933Q00120A002C001B012Q00029C002C00943Q00120A002C0041012Q00029C002C00953Q00120A002C0042012Q00029C002C00963Q00120A002C0043012Q00029C002C00973Q001255012C0044012Q00122Q002C0045012Q00122Q002D0046015Q002C0002000100122Q002C0028012Q00122Q002D0029012Q00122Q002E0047012Q00122Q002F0044015Q002C002F000100029C002C00983Q001255012C0048012Q00122Q002C0045012Q00122Q002D0046015Q002C0002000100122Q002C0028012Q00122Q002D0029012Q00122Q002E0049012Q00122Q002F0048015Q002C002F000100029C002C00993Q001255012C004A012Q00122Q002C0045012Q00122Q002D0046015Q002C0002000100122Q002C0028012Q00122Q002D0029012Q00122Q002E004B012Q00122Q002F004A015Q002C002F000100029C002C009A3Q001255012C004C012Q00122Q002C0045012Q00122Q002D0046015Q002C0002000100122Q002C0028012Q00122Q002D0029012Q00122Q002E004D012Q00122Q002F004C015Q002C002F000100029C002C009B3Q001255012C004E012Q00122Q002C0045012Q00122Q002D0046015Q002C0002000100122Q002C0028012Q00122Q002D004F012Q00122Q002E0050012Q00122Q002F004E015Q002C002F000100029C002C009C3Q001255012C0051012Q00122Q002C0045012Q00122Q002D0046015Q002C0002000100122Q002C0028012Q00122Q002D0029012Q00122Q002E0052012Q00122Q002F0051015Q002C002F0001000689012C009D000100052Q00583Q00144Q00583Q00124Q00583Q00114Q00583Q00154Q00583Q00173Q00120A002C0053012Q000689012C009E000100052Q00583Q00144Q00583Q00124Q00583Q00114Q00583Q00154Q00583Q00173Q00120A002C0054012Q0012FA002C0054013Q0062002C000100012Q00573Q00013Q009F3Q000E3Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F03153Q000A7365745F64656661756C745F636F6C6F727C606F03303Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C606346722Q65204B65792053797374656D7C6C6566747C03123Q000A612Q645F7370616365727C736D612Q6C7C037B3Q000A612Q645F736D612Q6C746578747C606354686973206973207468652057617665204B65792053797374656D2E20496620796F7520646F6E27742077616E7420746F206765742061206B65792C20796F752063616E206275792061205072656D69756D206F6E206F757220446973636F7264207365727665722E7C03263Q000A612Q645F746578745F696E7075747C6B65797C6032496E707574204B65793A2Q7C322Q307C031D3Q000A612Q645F62752Q746F6E7C6765746B65797C6034476574204B65797C03233Q000A612Q645F62752Q746F6E7C7375626D69746B65797C60325375626D6974204B65797C03253Q000A656E645F6469616C6F677C6B657973797374656D7C43616E63656C7C6034436C6F73657C030B3Q0053656E645661726C69737400124Q0010016Q00302B3Q0001000200302B3Q000300040012712Q0100063Q001271010200073Q00127B010300083Q00122Q000400093Q00122Q0005000A3Q00122Q000600083Q00122Q0007000B3Q00122Q0008000C3Q00122Q0009000D6Q00010001000900104Q0005000100122Q0001000E4Q005800026Q00442Q01000200012Q00573Q00017Q000E3Q0003063Q00612Q7365727403023Q00696F03053Q00706F70656E03013Q007203043Q007265616403023Q002A6103053Q00636C6F736503063Q00737472696E6703043Q006773756203043Q005E25732B034Q0003043Q0025732B2403053Q005B0A0D5D2B03013Q002002283Q001248000200013Q00122Q000300023Q00202Q0003000300034Q00045Q00122Q000500046Q000300056Q00023Q000200122Q000300013Q00202Q00040002000500122Q000600064Q00A1000400064Q00C500033Q00020020300004000200072Q004401040002000100068C2Q01001100013Q00043A012Q001100012Q0099000300023Q0012FA000400083Q00201B0104000400094Q000500033Q00122Q0006000A3Q00122Q0007000B6Q0004000700024Q000300043Q00122Q000400083Q00202Q0004000400094Q000500033Q00122Q0006000C3Q00122Q0007000B6Q0004000700024Q000300043Q00122Q000400083Q00202Q0004000400094Q000500033Q00122Q0006000D3Q00122Q0007000E6Q0004000700024Q000300046Q000300028Q00017Q000A3Q00028Q00030D3Q004F6E546578744F7665726C6179026Q00F03F031A3Q002060775B206063576176652050726F78792Q2060775D2Q20607703103Q004F6E436F6E736F6C654D652Q7361676503223Q002060305B60636473632E2Q672F7761766570726F787960305D606F20606F5B60772003043Q0020606F5D03053Q006E65746964026Q00F0BF030B3Q0053656E645661726C69737401164Q007F00018Q00025Q00302Q00020001000200122Q000300046Q00048Q00030003000400102Q00020003000300302Q00010001000500122Q000300066Q00045Q00122Q000500076Q00030003000500102Q00010003000300302Q00020008000900302Q00010008000900122Q0003000A6Q000400026Q00030002000100122Q0003000A6Q000400016Q0003000200016Q00017Q00083Q00028Q0003103Q004F6E436F6E736F6C654D652Q73616765026Q00F03F03223Q002060305B60636473632E2Q672F7761766570726F787960305D606F20606F5B60772003043Q0020606F5D03053Q006E65746964026Q00F0BF030B3Q0053656E645661726C697374010C4Q00102Q015Q00302B000100010002001271010200044Q005800035Q001271010400054Q006F01020002000400101D2Q010003000200302B0001000600070012FA000200084Q0058000300014Q00440102000200012Q00573Q00017Q00073Q002Q033Q00766172028Q00030D3Q004F6E546578744F7665726C6179026Q00F03F03053Q006E65746964026Q00F0BF030B3Q0053656E645661726C697374010C4Q00102Q015Q00120A000100013Q0012FA000100013Q00302B0001000200030012FA000100013Q00101D2Q0100043Q0012FA000100013Q00302B0001000500060012FA000100073Q0012FA000200014Q00442Q01000200012Q00573Q00017Q00093Q00034E3Q00682Q7470733A2F7261772E67697468756275736572636F6E74656E742E636F6D2F432Q6F6B696531322Q31322F73637269707467742F726566732F68656164732F6D61696E2F6B6579732E74787403023Q006F7303073Q006361707475726503083Q006375726C202D732003063Q00676D6174636803063Q007B282E2D297D03073Q005B5E2C25735D2B2Q0100011D3Q0012112Q0100013Q00122Q000200023Q00202Q00020002000300122Q000300046Q000400016Q0003000300044Q000400016Q0002000400024Q00035Q00202Q00040002000500122Q000600066Q00040006000600044Q00140001002030000800070005001271010A00074Q00F50008000A000A00043A012Q001200010020DB0003000B0008000614010800110001000100043A012Q001100010006140104000D0001000100043A012Q000D00012Q0084000400033Q0026590104001A0001000900043A012Q001A00012Q004F00046Q0005010400014Q0099000400024Q00573Q00017Q00043Q0003023Q00696F03053Q00777269746503083Q00636F6C6F72732Q7803053Q007265736574020A3Q0012FA000200013Q0020CC0002000200020012FA000300034Q00840003000300012Q005800045Q0012FA000500033Q0020CC0005000500042Q006F0103000300052Q00440102000200012Q00573Q00017Q00013Q0003093Q0052756E54687265616400043Q0012FA3Q00013Q00029C00016Q0044012Q000200012Q00573Q00013Q00013Q00193Q0003053Q006175746F632Q033Q006C6F6703203Q00605E4C6F636B2048617320422Q656E20436865636B65642042792050726F787903053Q00536C2Q6570025Q00C07240030C3Q004765744974656D436F756E74025Q00406E40025Q00C0584003043Q0074797065026Q00244003083Q00696E745F64617461030D3Q0053656E645061636B6574526177026Q005940025Q00109C40030A3Q0053656E645061636B6574027Q004003383Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C74656C6570686F6E650A6E756D7C35333738357C0A787C03053Q0074656C657803043Q007C0A797C03053Q0074656C6579031A3Q007C0A62752Q746F6E436C69636B65647C62676C636F6E76657274025Q0070A740025Q0014BC4003403Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C696E666F5F626F780A62752Q746F6E436C69636B65647C6D616B655F62676C025Q00408F4000383Q0012FA3Q00013Q00068C012Q003700013Q00043A012Q003700010012FA3Q00023Q00127E2Q0100038Q0002000100124Q00043Q00122Q000100058Q000200010012FA3Q00063Q0012712Q0100074Q00C63Q00020002000E390108001800013Q00043A012Q001800012Q0010016Q0030633Q0009000A00304Q000B000700122Q0001000C6Q00028Q00010002000100122Q000100043Q00122Q0002000D6Q00010002000100043A012Q000900010012FA3Q00063Q0012712Q01000E4Q00C63Q00020002000E390108002A00013Q00043A012Q002A00010012FA3Q000F3Q0012712Q0100103Q001271010200113Q0012FA000300123Q001271010400133Q0012FA000500143Q001271010600154Q006F0102000200062Q00EA3Q000200010012FA3Q00043Q0012712Q0100164Q0044012Q0002000100043A012Q001800010012FA3Q00063Q0012712Q0100174Q00C63Q00020002000E390108003700013Q00043A012Q003700010012FA3Q000F3Q0012132Q0100103Q00122Q000200188Q0002000100124Q00043Q00122Q000100198Q0002000100043A012Q002A00012Q00573Q00017Q00183Q0003023Q006F7303043Q006461746503053Q0025483A254D03043Q006773756203023Q00606F03023Q00606503023Q00607703023Q006030030D3Q00426C75652047656D204C6F636B030F3Q006065426C75652047656D204C6F636B030C3Q004469616D6F6E64204C6F636B030E3Q0060214469616D6F6E64204C6F636B030A3Q00576F726C64204C6F636B030C3Q006039576F726C64204C6F636B030E3Q00426C61636B2047656D204C6F636B03103Q006062426C61636B2047656D204C6F636B03193Q0043503A305F504C3A345F4F49443A5F43543A255B5342255D5F034Q0003173Q0043503A5F504C3A305F4F49443A5F43543A255B57255D5F03163Q00605E60625B605E616E7562656173743639233060625D03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203043Q0060775D20030C3Q007C6C6566747C37312Q387C0A030A3Q004C6F67436F2Q6C65637401333Q0012FA000100013Q0020CC000100010002001271010200034Q00C600010002000200203000023Q0004001271010400053Q001271010500064Q00C800020005000200202Q00020002000400122Q000400073Q00122Q000500086Q00020005000200202Q00020002000400122Q000400093Q00122Q0005000A6Q00020005000200202Q0002000200040012710104000B3Q0012710105000C4Q00C800020005000200202Q00020002000400122Q0004000D3Q00122Q0005000E6Q00020005000200202Q00020002000400122Q0004000F3Q00122Q000500106Q00020005000200202Q000200020004001271010400113Q001271010500126Q000200050002002030000200020004001271010400133Q001271010500126Q000200050002002030000200020004001271010400143Q001271010500126Q000200050002001271010300154Q0058000400013Q001271010500164Q0058000600023Q001271010700174Q006F0103000300070012FA000400184Q0058000500034Q006F01040004000500120A000400184Q00573Q00017Q00173Q0003023Q006F7303053Q00636C6F636B025Q00408F4003063Q0069706169727303043Q006E616D65028Q0003053Q007461626C6503063Q00696E7365727403023Q0060772Q033Q0020603003053Q00636F6C6F7203023Q006030030C3Q006032436F2Q6C65637465642003063Q00636F6E63617403073Q00206034416E642003053Q00536C2Q6570025Q00407F40030A3Q0053656E645061636B6574027Q004003133Q00616374696F6E7C696E7075740A7C746578747C03073Q007465787465746303013Q002003133Q006C6F67436F2Q6C65637465644D652Q7361676500423Q0012943Q00013Q00206Q00026Q0001000200206Q00034Q00018Q00013Q00014Q000200013Q00062Q0001000A0001000200043A012Q000A00012Q00573Q00014Q001A8Q00102Q016Q000501025Q0012FA000300044Q0059000400024Q004701030002000500043A012Q002400012Q0059000800033Q0020CC0009000700052Q008400080008000900068C0108002400013Q00043A012Q00240001000E39010600240001000800043A012Q002400012Q0005010200013Q0012FA000900073Q0020CC0009000900082Q0058000A00013Q001271010B00094Q0058000C00083Q001271010D000A3Q0020CC000E0007000B0020CC000F000700050012710110000C4Q006F010B000B00102Q00EA0009000B0001000614010300110001000200043A012Q0011000100068C0102003F00013Q00043A012Q003F00010012710103000D3Q0012C9000400073Q00202Q00040004000E4Q000500013Q00122Q0006000F6Q0004000600024Q00030003000400122Q000400103Q00122Q000500116Q00040002000100122Q000400123Q00122Q000500133Q00122Q000600143Q00122Q000700153Q00122Q000800166Q000900036Q0006000600094Q00040006000100122Q000400176Q000500036Q0004000200014Q00048Q000400034Q0005010300014Q0099000300024Q00573Q00017Q00113Q00028Q0003103Q004F6E436F6E736F6C654D652Q73616765026Q00F03F03043Q0066696E64030B3Q00606F436F2Q6C656374656403143Q0073686F77436F2Q6C6563746564456E61626C6564030A3Q00436865636B4C6F636B7303063Q0069706169727303043Q006E616D6503043Q006773756203013Q002003043Q002Q25732B03083Q00746F6E756D62657203053Q006D6174636803063Q002825642B292003063Q0063616E63656C03093Q0052756E54687265616401453Q0020CC00013Q00010026592Q0100420001000200043A012Q004200010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q01004200013Q00043A012Q004200010012FA000100063Q00068C2Q01004200013Q00043A012Q004200010012FA000100074Q00620001000100012Q00052Q015Q0012FA000200084Q005900036Q004701020002000400043A012Q003200010020CC00070006000900203201070007000A00122Q0009000B3Q00122Q000A000C6Q0007000A000200122Q0008000D3Q00202Q00093Q000300202Q00090009000E00122Q000B000F6Q000C00076Q000B000B000C2Q00A10009000B4Q00C500083Q000200068C0108003200013Q00043A012Q003200012Q00052Q0100014Q0059000900013Q0020CC000A000600092Q008400090009000A00062D0009002B0001000100043A012Q002B00012Q0059000900013Q0020CC000A000600090020DB0009000A00012Q0059000900013Q0020C3000A000600094Q000B00013Q00202Q000C000600094Q000B000B000C4Q000B000B00084Q0009000A000B000614010200130001000200043A012Q0013000100068C2Q01004000013Q00043A012Q004000012Q0059000200023Q00068C0102003C00013Q00043A012Q003C00012Q0059000200023Q0020300002000200102Q00440102000200010012FA000200113Q00029C00036Q00C60002000200022Q001A000200024Q0005010200014Q0099000200024Q00052Q016Q0099000100024Q00573Q00013Q00013Q00033Q0003053Q00536C2Q6570025Q00407F4003163Q0073656E64436F6C6F7265644C6F636B4D652Q7361676500063Q0012D73Q00013Q00122Q000100028Q0002000100124Q00038Q000100016Q00017Q00033Q0003043Q0066696E6403193Q00616374696F6E7C696E7075740A7C746578747C2F72656C6F6703093Q0052756E546872656164020D3Q002030000200010001001271010400026Q00020004000200068C0102000A00013Q00043A012Q000A00010012FA000200033Q00029C00036Q00440102000200012Q0005010200014Q0099000200024Q000501026Q0099000200024Q00573Q00013Q00013Q000D3Q0003083Q00476574576F726C6403043Q006E616D65030A3Q0053656E645061636B6574027Q004003443Q00616374696F6E7C696E7075740A7C746578747C603452656C6F67696E672C20602350726F78792042792060775B6063206473632E2Q672F7761766570726F78792060775D03073Q006F7665726D7367030A3Q00603452656C6F67696E6703053Q00536C2Q6570025Q00408F40026Q00084003063Q00737472696E6703063Q00666F726D6174032A3Q00616374696F6E7C6A6F696E5F726571756573740A6E616D657C25730A696E7669746564576F726C647C3000163Q00128A3Q00018Q0001000200206Q000200122Q000100033Q00122Q000200043Q00122Q000300056Q00010003000100122Q000100063Q00122Q000200076Q0001000200010012FA000100083Q001271010200094Q00442Q01000200010012FA000100033Q0012710102000A3Q0012FA0003000B3Q0020CC00030003000C0012710104000D4Q005800056Q00A1000300054Q005D00013Q00012Q00573Q00017Q00033Q0003043Q0066696E6403203Q00616374696F6E7C696E7075740A7C746578747C2F652Q6665637464656C65746503093Q0052756E546872656164020D3Q002030000200010001001271010400026Q00020004000200068C0102000A00013Q00043A012Q000A00010012FA000200033Q00029C00036Q00440102000200012Q0005010200014Q0099000200024Q000501026Q0099000200024Q00573Q00013Q00013Q00083Q00030A3Q0053656E645061636B6574027Q004003483Q00616374696F6E7C696E7075740A7C746578747C6034507572676520452Q666563742C20602350726F78792042792060775B6063206473632E2Q672F7761766570726F78792060775D03073Q006F7665726D736703113Q00603444656C6574696E6720452Q6665637403053Q00536C2Q6570025Q00408F4003203Q00616374696F6E7C696E7075740A7C746578747C2F6D6F64616765205Q39000F3Q0012FA3Q00013Q0012132Q0100023Q00122Q000200038Q0002000100124Q00043Q00122Q000100058Q000200010012FA3Q00063Q0012712Q0100074Q0044012Q000200010012FA3Q00013Q0012712Q0100023Q001271010200084Q00EA3Q000200012Q00573Q00017Q00083Q0003043Q0066696E64030E3Q00616374696F6E7C7265737061776E03173Q00616374696F6E7C696E7075740A7C746578747C2F72657303073Q006F7665726D736703093Q0060345265737061776E030A3Q0053656E645061636B6574027Q004003453Q00616374696F6E7C696E7075740A7C746578747C60345265737061776E65642C20602350726F78792042792060775B6063206473632E2Q672F7761766570726F78792060775D021A3Q002030000200010001001271010400026Q00020004000200062D0002000A0001000100043A012Q000A0001002030000200010001001271010400036Q00020004000200068C0102001700013Q00043A012Q001700010012FA000200043Q001271010300054Q00440102000200010012FA000200063Q001271010300073Q001271010400024Q00EA0002000400010012FA000200063Q001271010300073Q001271010400084Q00EA0002000400012Q0005010200014Q0099000200024Q000501026Q0099000200024Q00573Q00017Q00013Q0003093Q0052756E54687265616401053Q0012FA000100013Q00068901023Q000100012Q00588Q00442Q01000200012Q00573Q00013Q00013Q00123Q0003043Q006D61746803053Q00666C2Q6F72030C3Q004765744974656D436F756E74025Q0014BC40030A3Q0053656E645061636B6574027Q004003433Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C696E666F5F626F780A62752Q746F6E436C69636B65647C6D616B655F626C7565676C03053Q00536C2Q6570026Q00594003383Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C62616E6B5F6465706F7369740A62676C5F636F756E747C03123Q00616374696F6E7C696E7075740A746578747C03073Q0074657874657463030F3Q002060394465706F736974656420603203083Q00746F737472696E6703113Q00206065426C75652047656D204C6F636B7303073Q006F7665726D7367030E3Q0060394465706F736974656420603203103Q00206065426C75652047656D204C6F636B002E3Q0012C23Q00013Q00206Q000200122Q000100033Q00122Q000200046Q000100029Q00000200122Q000100013Q00202Q0001000100024Q00028Q00010002000200064Q00130001000100043A012Q001300010012FA3Q00053Q0012132Q0100063Q00122Q000200078Q0002000100124Q00083Q00122Q000100098Q000200010012FA3Q00053Q0012752Q0100063Q00122Q0002000A6Q00038Q0002000200036Q0002000100124Q00053Q00122Q000100063Q00122Q0002000B3Q00122Q0003000C3Q00122Q0004000D3Q0012FA0005000E3Q0012FA000600013Q0020CC0006000600022Q005900076Q000A010600074Q00C500053Q00020012710106000F4Q006F0102000200062Q00EA3Q000200010012FA3Q00103Q0012712Q0100114Q005900025Q001271010300124Q006F2Q01000100032Q0044012Q000200012Q00573Q00017Q00013Q0003093Q0052756E54687265616400043Q0012FA3Q00013Q00029C00016Q0044012Q000200012Q00573Q00013Q00013Q00093Q0003053Q00536C2Q6570026Q006940030C3Q004765744974656D436F756E74025Q008FC640028Q00030A3Q0053656E645061636B6574027Q004003433Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C696E666F5F626F780A62752Q746F6E436C69636B65647C6D616B655F626C7565676C026Q00794000193Q00029C8Q000B00018Q00010001000100122Q000100013Q00122Q000200026Q0001000200010012FA000100033Q001271010200044Q00C6000100020002000E39010500180001000100043A012Q001800010012FA000100063Q001240010200073Q00122Q000300086Q00010003000100122Q000100013Q00122Q000200096Q0001000200014Q00018Q00010001000100122Q000100013Q00122Q000200026Q00010002000100044Q000600012Q00573Q00013Q00013Q000A3Q00030C3Q004765744974656D436F756E74025Q0014BC40030A3Q0053656E645061636B6574027Q004003383Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C62616E6B5F6465706F7369740A62676C5F636F756E747C03123Q00616374696F6E7C696E7075740A746578747C03073Q007465787465746303233Q002060394465706F7369746564206034412Q6C206065426C75652047656D204C6F636B7303073Q006F7665726D736703213Q0060394465706F7369746564206034412Q6C206065426C75652047656D204C6F636B00143Q0012FA3Q00013Q0012712Q0100024Q00C63Q000200020012FA000100033Q001271010200043Q001271010300054Q005800046Q006F0103000300042Q00EA0001000300010012FA000100033Q0012B5000200043Q00122Q000300063Q00122Q000400073Q00122Q000500086Q0003000300054Q0001000300010012FA000100093Q0012710102000A4Q00442Q01000200012Q00573Q00017Q00013Q0003093Q0052756E54687265616401053Q0012FA000100013Q00068901023Q000100012Q00588Q00442Q01000200012Q00573Q00013Q00013Q000F3Q00030A3Q0053656E645061636B6574027Q004003393Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C62616E6B5F77697468647261770A62676C5F636F756E747C03123Q00616374696F6E7C696E7075740A746578747C03073Q0074657874657463030E3Q00206039576974686472657720603203083Q00746F737472696E6703043Q006D61746803053Q00666C2Q6F7203113Q00206039426C75652047656D204C6F636B73030D3Q004F6E546578744F7665726C6179030D3Q006039576974686472657720603203113Q00603920426C75652047656D204C6F636B732Q033Q006C6F67030A3Q00436865636B4C6F636B73002D3Q001207012Q00013Q00122Q000100023Q00122Q000200036Q00038Q0002000200036Q0002000100124Q00013Q00122Q000100023Q00122Q000200043Q00122Q000300053Q00122Q000400063Q00122Q000500073Q00122Q000600083Q00202Q0006000600094Q00078Q000600076Q00053Q000200122Q0006000A6Q0002000200066Q0002000100124Q000B3Q00122Q0001000C3Q00122Q000200073Q00122Q000300083Q00202Q0003000300094Q00048Q000300046Q00023Q000200122Q0003000D6Q0001000100036Q0002000100124Q000E3Q00122Q0001000C3Q00122Q000200073Q00122Q000300083Q00202Q0003000300094Q00048Q000300046Q00023Q000200122Q0003000D6Q0001000100036Q0002000100124Q000F8Q000100016Q00017Q00073Q00027Q004003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F64702003063Q00737472696E6703053Q006D61746368031C3Q00616374696F6E7C696E7075740A7C746578747C2F6470202825642B2903163Q00616374696F6E7C696E7075740A7C746578747C2F6470021E3Q002659012Q001B0001000100043A012Q001B0001002030000200010002001271010400036Q00020004000200068C0102001200013Q00043A012Q001200010012FA000200043Q0020620102000200054Q000300013Q00122Q000400066Q0002000400024Q00038Q000400026Q0003000200014Q000300016Q000300023Q00044Q001B0001002030000200010002001271010400076Q00020004000200068C0102001B00013Q00043A012Q001B00012Q0059000200014Q00620002000100012Q0005010200014Q0099000200024Q000501026Q0099000200024Q00573Q00017Q00083Q00027Q004003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F77642003173Q00616374696F6E7C696E7075740A7C746578747C2F57442003063Q00737472696E6703053Q006D61746368031C3Q00616374696F6E7C696E7075740A7C746578747C2F7764202825642B29031C3Q00616374696F6E7C696E7075740A7C746578747C2F5744202825642B2902203Q002659012Q001D0001000100043A012Q001D0001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102001D00013Q00043A012Q001D00010012FA000200053Q0020670002000200064Q000300013Q00122Q000400076Q00020004000200062Q000200180001000100043A012Q001800010012FA000200053Q0020CC0002000200062Q0058000300013Q001271010400086Q0002000400022Q005900036Q0058000400024Q00440103000200012Q0005010300014Q0099000300024Q000501026Q0099000200024Q00573Q00017Q000D3Q00030C3Q004D6F64657261746F72766172028Q0003113Q004F6E412Q644E6F74696669636174696F6E026Q00F03F031D3Q00696E746572666163652F61746F6D69635F62752Q746F6E2E722Q746578027Q004003243Q0060775B606320576176652050726F78792060775D206034414C5741595320464F4355532E026Q00084003123Q00617564696F2F6875625F6F70656E2E776176026Q00104003053Q006E65746964026Q00F0BF030B3Q0053656E645661726C69737400124Q0010016Q00120A3Q00013Q0012FA3Q00013Q00302B3Q000200030012FA3Q00013Q00302B3Q000400050012FA3Q00013Q00302B3Q000600070012FA3Q00013Q00302B3Q000800090012FA3Q00013Q0030AA3Q000A000200124Q00013Q00304Q000B000C00124Q000D3Q00122Q000100018Q000200016Q00017Q00063Q00028Q0003103Q004F6E436F6E736F6C654D652Q73616765026Q00F03F03043Q0066696E64030C3Q00576F726C64204C6F636B656403093Q0052756E546872656164010E3Q0020CC00013Q00010026592Q01000D0001000200043A012Q000D00010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q01000D00013Q00043A012Q000D00010012FA000100063Q00068901023Q000100012Q00588Q00442Q01000200012Q00573Q00013Q00013Q00243Q0003053Q00536C2Q6570025Q00708740030D3Q004F6E546578744F7665726C6179034Q00026Q00F03F03083Q007761726E696E6732030A3Q0053656E645061636B6574027Q0040032A3Q00616374696F6E7C696E7075740A7C746578747C60775B606320576176652050726F78792060775D2Q206003043Q006D61746803063Q0072616E646F6D028Q00026Q00224003053Q00596F75206003043Q00476F206003043Q00546F2060030B3Q00574F524C442060623A206003083Q00476574576F726C6403043Q006E616D65025Q00408F40030B3Q00776C5F62616C616E63657303053Q00666C2Q6F72030C3Q004765744974656D436F756E74025Q00406E40030B3Q00646C5F62616C616E636573025Q00109C40030C3Q0062676C5F62616C616E636573025Q0014BC40030E3Q006972656E675F62616C616E636573025Q008FC640033A3Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2Q20603942616C616E6365206063574C3A206034030D3Q0020606226206063444C3A206034030E3Q002060622620606342474C3A20603403103Q00206062262060634952454E473A20603403073Q007761726E696E6703063Q006E692Q676172006C3Q00129A3Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100046Q00025Q00202Q00020002000500122Q000300046Q0001000100036Q0002000100124Q00033Q00122Q000100046Q00025Q00202Q00020002000500122Q000300046Q0001000100036Q0002000100124Q00063Q00064Q006600013Q00043A012Q006600010012FA3Q00073Q0012712Q0100083Q00128F010200093Q00122Q0003000A3Q00202Q00030003000B00122Q0004000C3Q00122Q0005000D6Q00030005000200122Q0004000E3Q00122Q0005000A3Q00202Q00050005000B00122Q0006000C3Q0012710107000D6Q00050007000200128F0106000F3Q00122Q0007000A3Q00202Q00070007000B00122Q0008000C3Q00122Q0009000D6Q00070009000200122Q000800103Q00122Q0009000A3Q00202Q00090009000B00122Q000A000C3Q001271010B000D6Q0009000B0002001271010A00113Q0012FA000B000A3Q0020CC000B000B000B001271010C000C3Q001271010D000D6Q000B000D0002001271010C00043Q0012FA000D00124Q0085010D0001000200202Q000D000D001300122Q000E00046Q00020002000E6Q0002000100124Q00013Q00122Q000100148Q0002000100124Q000A3Q00206Q00160012FA000100173Q001295010200186Q000100029Q00000200124Q00153Q00124Q000A3Q00206Q001600122Q000100173Q00122Q0002001A6Q000100029Q00000200120A3Q00193Q0012FA3Q000A3Q0020CC5Q00160012FA000100173Q0012950102001C6Q000100029Q00000200124Q001B3Q00124Q000A3Q00206Q001600122Q000100173Q00122Q0002001E6Q000100029Q00000200120A3Q001D3Q0012FA3Q00073Q0012712Q0100083Q0012710102001F3Q0012FA000300153Q001271010400203Q0012FA000500193Q001271010600213Q0012FA0007001B3Q001271010800223Q0012FA0009001D4Q006F0102000200092Q00EA3Q000200010012FA3Q00233Q00068C012Q006B00013Q00043A012Q006B00010012FA3Q00244Q00623Q000100012Q00573Q00017Q00023Q00030A3Q0053656E645061636B6574027Q004002073Q001224010200013Q00122Q000300026Q00048Q0002000400014Q000200016Q000200028Q00017Q00023Q00027Q004003053Q006D61746368050F3Q002659012Q000C0001000100043A012Q000C00010020300005000100022Q0058000700026Q00050007000200068C0105000C00013Q00043A012Q000C00012Q0058000600034Q0058000700054Q0058000800045Q00010600084Q003401066Q000501056Q0099000500024Q00573Q00017Q001C3Q0003223Q00616374696F6E7C696E7075740A7C746578747C2F5B44645D5B53735D202825642B29031E3Q00616374696F6E7C696E7075740A7C746578747C2F5B50705D202825772B29031E3Q00616374696F6E7C696E7075740A7C746578747C2F5B4B6B5D202825772B29031E3Q00616374696F6E7C696E7075740A7C746578747C2F5B54745D202825772B2903053Q006D6174636803243Q00616374696F6E7C696E7075740A7C746578747C2F5B42625D5B41615D5B4E6E5D5B4B6B5D03393Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C706F7075700A62752Q746F6E436C69636B65647C62676C7303093Q00536176652042616E6B03183Q00616374696F6E7C696E7075740A7C746578747C2F5B47675D03193Q00616374696F6E7C696E7075740A7C746578747C2F67686F7374030A3Q0047686F7374204D6F646503283Q00616374696F6E7C696E7075740A7C746578747C2F5B42625D5B4C6C5D5B41615D5B43635D5B4B6B5D03283Q00616374696F6E7C696E7075740A7C746578747C2F5B48685D5B49695D5B54745D5B41615D5B4D6D5D030A3Q0053656E645061636B6574027Q004003403Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C696E666F5F626F780A62752Q746F6E436C69636B65647C6D616B655F62676C03123Q00616374696F6E7C696E7075740A746578747C03073Q007465787465746303253Q0020603953752Q63652Q7320436F6E7665727420606342474C206034546F206062426C61636B03073Q006F7665726D736703243Q00603953752Q63652Q7320436F6E7665727420606342474C206034546F206062426C61636B03243Q00616374696F6E7C696E7075740A7C746578747C2F5B42625D5B4C6C5D5B55755D5B45655D03433Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C696E666F5F626F780A62752Q746F6E436C69636B65647C6D616B655F626C7565676C03383Q0020603953752Q63652Q7320436F6E76657274206062426C61636B2047656D204C6F636B206034546F206063426C75652047656D204C6F636B03373Q00603953752Q63652Q7320436F6E76657274206062426C61636B2047656D204C6F636B206034546F206063426C75652047656D204C6F636B031E3Q00616374696F6E7C696E7075740A7C746578747C2F5B4E6E5D202825772B2903223Q00616374696F6E7C696E7075740A7C746578747C2F5B57775D5B54745D202825772B29031E3Q00616374696F6E7C696E7075740A7C746578747C2F5B57775D202825772B2902924Q005900026Q005800036Q0058000400013Q001271010500013Q00029C00068Q00020006000200068C0102000A00013Q00043A012Q000A00012Q0005010200014Q0099000200024Q005900026Q005800036Q0058000400013Q001271010500023Q00068901060001000100012Q00593Q00016Q00020006000200068C0102001500013Q00043A012Q001500012Q0005010200014Q0099000200024Q005900026Q005800036Q0058000400013Q001271010500033Q00068901060002000100012Q00593Q00016Q00020006000200068C0102002000013Q00043A012Q002000012Q0005010200014Q0099000200024Q005900026Q005800036Q0058000400013Q001271010500043Q00068901060003000100012Q00593Q00016Q00020006000200068C0102002B00013Q00043A012Q002B00012Q0005010200014Q0099000200023Q002030000200010005001271010400066Q00020004000200068C0102003500013Q00043A012Q003500012Q0059000200013Q001271010300073Q001271010400085Q00010200044Q003401025Q002030000200010005001271010400096Q00020004000200068C0102003F00013Q00043A012Q003F00012Q0059000200013Q0012710103000A3Q0012710104000B5Q00010200044Q003401025Q0020300002000100050012710104000C6Q00020004000200062D000200490001000100043A012Q004900010020300002000100050012710104000D6Q00020004000200068C0102005900013Q00043A012Q005900010012FA0002000E3Q00120E0003000F3Q00122Q000400106Q00020004000100122Q0002000E3Q00122Q0003000F3Q00122Q000400113Q00122Q000500123Q00122Q000600136Q0004000400064Q00020004000100122Q000200143Q00122Q000300156Q0002000200014Q000200016Q000200023Q002030000200010005001271010400166Q00020004000200068C0102006E00013Q00043A012Q006E00010012FA0002000E3Q00120E0003000F3Q00122Q000400176Q00020004000100122Q0002000E3Q00122Q0003000F3Q00122Q000400113Q00122Q000500123Q00122Q000600186Q0004000400064Q00020004000100122Q000200143Q00122Q000300196Q0002000200014Q000200016Q000200024Q005900026Q005800036Q0058000400013Q0012710105001A3Q00068901060004000100012Q00593Q00016Q00020006000200068C0102007900013Q00043A012Q007900012Q0005010200014Q0099000200024Q005900026Q005800036Q0058000400013Q0012710105001B3Q00068901060005000100012Q00593Q00016Q00020006000200068C0102008400013Q00043A012Q008400012Q0005010200014Q0099000200024Q005900026Q005800036Q0058000400013Q0012710105001C3Q00068901060006000100012Q00593Q00016Q00020006000200068C0102008F00013Q00043A012Q008F00012Q0005010200014Q0099000200024Q000501026Q0099000200024Q00573Q00013Q00073Q00103Q0003083Q00746F6E756D626572030C3Q004765744974656D436F756E74025Q00FCB140030A3Q0053656E645061636B6574027Q004003063Q00737472696E6703063Q00666F726D617403433Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C64726F700A6974656D5F64726F707C343630347C0A6974656D5F636F756E747C256403163Q00603944726F2Q7065642060322564206039412Q726F7A03123Q00616374696F6E7C696E7075740A746578747C03073Q007465787465746303013Q0020030D3Q004F6E546578744F7665726C61792Q033Q006C6F67031A3Q0060394E6F7420656E6F75676820412Q726F7A20746F2064726F7003283Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2Q2001353Q00125B2Q0100016Q00028Q0001000200026Q00013Q00122Q000100023Q00122Q000200036Q00010002000200064Q00250001000100043A012Q002500010012FA000100043Q001271010200053Q0012FA000300063Q0020CC000300030007001271010400084Q005800056Q00A1000300054Q005D00013Q00010012FA000100063Q0020CC000100010007001271010200094Q005800038Q0001000300020012FA000200043Q001271010300053Q0012710104000A3Q0012FA0005000B3Q0012710106000C4Q0058000700014Q006F0104000400072Q00EA0002000400010012FA0002000D4Q0058000300014Q005E01020002000100122Q0002000E6Q000300016Q00020002000100044Q003200010012712Q01000F3Q0012A3010200043Q00122Q000300053Q00122Q000400106Q000500016Q0004000400054Q00020004000100122Q0002000D6Q000300016Q00020002000100122Q0002000E4Q0058000300014Q00440102000200012Q00052Q0100014Q0099000100024Q00573Q00017Q00023Q0003183Q00616374696F6E7C696E7075740A746578747C2F70752Q6C2003083Q0050752Q6C696E6720010A4Q000C00015Q00122Q000200016Q00038Q00020002000300122Q000300026Q00048Q0003000300044Q000100036Q00019Q0000017Q00023Q0003183Q00616374696F6E7C696E7075740A746578747C2F6B69636B2003083Q004B69636B696E6720010A4Q000C00015Q00122Q000200016Q00038Q00020002000300122Q000300026Q00048Q0003000300044Q000100036Q00019Q0000017Q00023Q0003193Q00616374696F6E7C696E7075740A746578747C2F747261646520030D3Q0054726164696E67207769746820010A4Q000C00015Q00122Q000200016Q00038Q00020002000300122Q000300026Q00048Q0003000300044Q000100036Q00019Q0000017Q00023Q0003183Q00616374696F6E7C696E7075740A746578747C2F6E69636B20031D3Q0053752Q63652Q7366752Q6C79204368616E676564204E69636B20546F20010A4Q000C00015Q00122Q000200016Q00038Q00020002000300122Q000300026Q00048Q0003000300044Q000100036Q00019Q0000017Q00023Q00031A3Q00616374696F6E7C696E7075740A746578747C2F77617270746F2003153Q0053752Q63652Q7366752Q6C79205761727020546F20010A4Q000C00015Q00122Q000200016Q00038Q00020002000300122Q000300026Q00048Q0003000300044Q000100036Q00019Q0000017Q00023Q0003183Q00616374696F6E7C696E7075740A746578747C2F776172702003153Q0053752Q63652Q7366752Q6C79205761727020546F20010A4Q000C00015Q00122Q000200016Q00038Q00020002000300122Q000300026Q00048Q0003000300044Q000100036Q00019Q0000017Q00033Q0003063Q00737472696E6703063Q00666F726D617403133Q00603944726F2Q7065642060322564206039257302083Q001281010200013Q00202Q00020002000200122Q000300036Q000400016Q00058Q000200056Q00029Q0000017Q000D3Q00030C3Q004765744974656D436F756E74030A3Q0053656E645061636B6574027Q004003063Q00737472696E6703063Q00666F726D617403413Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C64726F700A6974656D5F64726F707C25647C0A6974656D5F636F756E747C256403123Q00616374696F6E7C696E7075740A746578747C03073Q007465787465746303013Q0020030D3Q004F6E546578744F7665726C61792Q033Q006C6F6703173Q0060344E6F7420656E6F75676820257320746F2064726F7003283Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2Q2003353Q0012FA000300014Q005800046Q00C6000300020002000605000200210001000300043A012Q002100010012FA000300023Q001239000400033Q00122Q000500043Q00202Q00050005000500122Q000600066Q00078Q000800026Q000500086Q00033Q00014Q00038Q000400014Q0058000500026Q0003000500020012FA000400023Q001271010500033Q001271010600073Q0012FA000700083Q001271010800094Q0058000900034Q006F0106000600092Q00EA0004000600010012FA0004000A4Q0058000500034Q005E01040002000100122Q0004000B6Q000500036Q00040002000100044Q003200010012FA000300043Q0020CC0003000300050012710104000C4Q0058000500016Q0003000500020012A3010400023Q00122Q000500033Q00122Q0006000D6Q000700036Q0006000600074Q00040006000100122Q0004000A6Q000500036Q00040002000100122Q0004000B4Q0058000500034Q00440104000200012Q0005010300014Q0099000300024Q00573Q00017Q00143Q00027Q004003053Q006D6174636803223Q00616374696F6E7C696E7075740A7C746578747C2F5B44645D5B43635D202825642B2903063Q00434C4F56455203063Q00436C6F76657203083Q00746F6E756D62657203283Q00616374696F6E7C696E7075740A7C746578747C2F5B4D6D5D5B4F6F5D5B44645D5B41615D5B4C6C5D03053Q00706169727303043Q006D61746803053Q00666C2Q6F72030C3Q004765744974656D436F756E7403063Q00737472696E6703063Q00666F726D6174035C3Q0060775B606320576176652050726F78792060775D3Q20603942616C616E6365206063574C3A206034256420606226206063444C3A20603425642060622620606342474C3A2060342564206062262060634952454E473A206034256403023Q00574C03023Q00444C2Q033Q0042474C03053Q004952454E47030A3Q0053656E645061636B657403123Q00616374696F6E7C696E7075740A746578747C023A3Q002659012Q00100001000100043A012Q00100001002030000200010002001271010400036Q00020004000200068C0102001000013Q00043A012Q001000012Q005900036Q0059000400013Q0020CC000400040004001271010500053Q0012FA000600064Q0058000700024Q000A010600074Q006E00036Q003401035Q002659012Q00370001000100043A012Q00370001002030000200010002001271010400076Q00020004000200068C0102003700013Q00043A012Q003700012Q001001025Q0012FA000300084Q0059000400014Q004701030002000500043A012Q0025000100265B000600250001000400043A012Q002500010012FA000800093Q00201701080008000A00122Q0009000B6Q000A00076Q0009000A6Q00083Q00024Q0002000600080006140103001C0001000200043A012Q001C00010012FA0003000C3Q0020CC00030003000D0012710104000E3Q0020CC00050002000F0020CC0006000200100020CC0007000200110020CC0008000200124Q0003000800020012FA000400133Q001271010500013Q001271010600144Q0058000700034Q006F0106000600072Q00EA0004000600012Q0005010400014Q0099000400024Q000501026Q0099000200024Q00573Q00017Q00063Q00028Q0003043Q0066696E64030D3Q004F6E534442726F616463617374030D3Q004F6E546578744F7665726C617903253Q0060775B606320576176652050726F78792060775D206063424C4F434B45442053444220212003243Q0060775B606320576176652050726F78792060775D206063424C4F434B4544205344422021010F3Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001000E00013Q00043A012Q000E00010012FA000100043Q00127E010200056Q00010002000100122Q000100043Q00122Q000200066Q0001000200012Q00052Q0100014Q0099000100024Q00573Q00017Q00063Q00028Q0003043Q0066696E64030C3Q004F6E54616C6B42752Q626C65027Q0040030E3Q0028742Q6F2066617220617761792903093Q0052756E54687265616401123Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001001100013Q00043A012Q001100010020CC00013Q0004002030000100010002001271010300056Q00010003000200068C2Q01001100013Q00043A012Q001100010012FA000100063Q00029C00026Q00442Q01000200012Q00052Q0100014Q0099000100024Q00573Q00013Q00013Q00023Q0003053Q00536C2Q6570025Q0088B34000043Q0012FA3Q00013Q0012712Q0100024Q0044012Q000200012Q00573Q00017Q00053Q00028Q0003043Q0066696E64030C3Q004F6E54616C6B42752Q626C65027Q004003183Q004E657720637573746F6D20736B696E20612Q706C6965642E010F3Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001000E00013Q00043A012Q000E00010020CC00013Q0004002030000100010002001271010300056Q00010003000200068C2Q01000E00013Q00043A012Q000E00012Q00052Q0100014Q0099000100024Q00573Q00017Q00053Q00028Q0003043Q0066696E6403103Q004F6E436F6E736F6C654D652Q73616765026Q00F03F03183Q004E657720637573746F6D20736B696E20612Q706C6965642E010F3Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001000E00013Q00043A012Q000E00010020CC00013Q0004002030000100010002001271010300056Q00010003000200068C2Q01000E00013Q00043A012Q000E00012Q00052Q0100014Q0099000100024Q00573Q00017Q00053Q00028Q0003043Q0066696E64030F3Q004F6E4469616C6F6752657175657374026Q00F03F031A3Q00576F772C2074686174277320666173742064656C69766572792E010F3Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001000E00013Q00043A012Q000E00010020CC00013Q0004002030000100010002001271010300056Q00010003000200068C2Q01000E00013Q00043A012Q000E00012Q00052Q0100014Q0099000100024Q00573Q00017Q00063Q00028Q0003043Q0066696E64030C3Q004F6E54616C6B42752Q626C65027Q0040031A3Q00596F7520676F74206024426C75652047656D204C6F636B2Q602103093Q0052756E54687265616401123Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001001100013Q00043A012Q001100010020CC00013Q0004002030000100010002001271010300056Q00010003000200068C2Q01001100013Q00043A012Q001100010012FA000100063Q00029C00026Q00442Q01000200012Q00052Q0100014Q0099000100024Q00573Q00013Q00013Q00043Q0003053Q00536C2Q6570025Q00408F40030D3Q004F6E546578744F7665726C6179034A3Q0060775B606320576176652050726F78792060775D205B206032436F6E7665727465642060214469616D6F6E64204C6F636B206032546F206065426C75652047656D204C6F636B2060775D00073Q00129D012Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100048Q000200016Q00017Q00093Q00028Q0003103Q004F6E436F6E736F6C654D652Q73616765026Q00F03F03043Q0066696E6403123Q006034556E6B6E6F776E20636F2Q6D616E642E030D3Q004F6E546578744F7665726C6179033C3Q006035446F20547970652060392F6D656E75206F72202F70726F7879206035466F722053686F777320412Q6C2050726F787920436F2Q6D616E64732E20033B3Q006035446F20547970652060392F6D656E75206F72202F70726F7879206035466F722053686F777320412Q6C2050726F787920436F2Q6D616E64732E2Q033Q006C6F6701153Q0020CC00013Q00010026592Q0100140001000200043A012Q001400010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q01001400013Q00043A012Q001400010012FA000100063Q0012B1000200076Q00010002000100122Q000100063Q00122Q000200086Q00010002000100122Q000100093Q00122Q000200086Q0001000200014Q000100016Q000100024Q00573Q00017Q00103Q00028Q0003043Q0066696E64030F3Q004F6E4469616C6F6752657175657374026Q00F03F032C3Q004469616C2061206E756D62657220746F2063612Q6C20736F6D65626F647920696E2047726F77746F7069612E03043Q0066617374030B3Q0054454C4550484F4E455F5803053Q006D6174636803123Q00656D6265645F646174617C787C2825642B29030B3Q0054454C4550484F4E455F5903123Q00656D6265645F646174617C797C2825642B29030A3Q0053656E645061636B6574027Q004003383Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C74656C6570686F6E650A6E756D7C35333738357C0A787C03043Q007C0A797C031A3Q007C0A62752Q746F6E436C69636B65647C62676C636F6E7665727401273Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001002400013Q00043A012Q002400010020CC00013Q0004002030000100010002001271010300056Q00010003000200068C2Q01002400013Q00043A012Q002400010012FA000100063Q00068C2Q01002400013Q00043A012Q002400010020CC00013Q00040020D100010001000800122Q000300096Q00010003000200122Q000100073Q00202Q00013Q000400202Q00010001000800122Q0003000B6Q00010003000200122Q0001000A3Q00122Q0001000C3Q00122Q0002000D3Q00122Q0003000E3Q00122Q000400073Q00122Q0005000F3Q00122Q0006000A3Q00122Q000700106Q0003000300074Q0001000300014Q000100016Q000100024Q00052Q016Q0099000100024Q00573Q00017Q00053Q00028Q0003103Q004F6E436F6E736F6C654D652Q73616765026Q00F03F03043Q0066696E6403163Q007361696420736F6D657468696E6720692Q6C6567616C010C3Q0020CC00013Q00010026592Q01000B0001000200043A012Q000B00010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q01000B00013Q00043A012Q000B00012Q00052Q0100014Q0099000100024Q00573Q00017Q000E3Q00027Q004003043Q0066696E6403053Q002F74656C6503053Q002F54454C4503053Q0074656C657803083Q004765744C6F63616C03053Q00706F735F78026Q002Q4003053Q0074656C657903053Q00706F735F79030D3Q004F6E546578744F7665726C617903353Q0060775B20606354656C6570686F6E65206032466F722060344175746F2060634320603142474C206032536574206034212060775D2003343Q0060775B20606354656C6570686F6E65206032466F722060344175746F2060634320603142474C206032536574206034212060775D2Q033Q006C6F6702223Q000E240001000700013Q00043A012Q00070001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102002100013Q00043A012Q002100010012FA000200064Q002A00020001000200202Q00020002000700202Q00020002000800122Q000200053Q00122Q000200066Q00020001000200202Q00020002000A00202Q00020002000800122Q000200093Q00122Q0002000B3Q00122Q0003000C6Q00020002000100122Q0002000B3Q00122Q0003000D6Q00020002000100122Q0002000E3Q00122Q0003000D6Q0002000200014Q000200016Q000200024Q00573Q00017Q00243Q0003053Q006972656E6703013Q0072028Q0003013Q006703013Q006203013Q007403073Q006D652Q7361676503283Q005B20576176652050726F7879205D205B20536B696E204972656E672053752Q63652Q7366756C205D2Q033Q00726564026Q00594003263Q005B20576176652050726F7879205D205B20536B696E205265642053752Q63652Q7366756C205D03053Q0067722Q656E03283Q005B20576176652050726F7879205D205B20536B696E2047722Q656E2053752Q63652Q7366756C205D03043Q00626C756503273Q005B20576176652050726F7879205D205B20536B696E20426C75652053752Q63652Q7366756C205D031D3Q00616374696F6E7C696E7075740A7C746578747C2F6972656E67736B696E031D3Q00616374696F6E7C696E7075740A7C746578747C2F4952454E47534B494E031E3Q00616374696F6E7C696E7075740A7C746578747C2F736B696E206972656E67031E3Q00616374696F6E7C696E7075740A7C746578747C2F534B494E204952454E47031C3Q00616374696F6E7C696E7075740A7C746578747C2F736B696E20726564031C3Q00616374696F6E7C696E7075740A7C746578747C2F534B494E20524544031E3Q00616374696F6E7C696E7075740A7C746578747C2F736B696E2067722Q656E031E3Q00616374696F6E7C696E7075740A7C746578747C2F534B494E2047522Q454E031D3Q00616374696F6E7C696E7075740A7C746578747C2F736B696E20626C7565031D3Q00616374696F6E7C696E7075740A7C746578747C2F534B494E20424C554503053Q00706169727303063Q00697061697273027Q004003043Q0066696E64030D3Q004F6E546578744F7665726C6179030D3Q00606F53752Q63652Q7366756C20030C3Q00606F53752Q63652Q7366756C030A3Q0053656E645061636B657403063Q00737472696E6703063Q00666F726D617403533Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C736B696E7069636B65720A7265647C25640A67722Q656E7C25640A626C75657C25640A7472616E73706172656E63797C2564025B4Q001001023Q00042Q001001033Q000500302B00030002000300302B00030004000300302B00030005000300302B00030006000300302B00030007000800101D0102000100032Q001001033Q000500302B00030002000A00302B00030004000300302B00030005000300302B00030006000300302B00030007000B00101D0102000900032Q001001033Q000500302B00030002000300302B00030004000A00302B00030005000300302B00030006000300302B00030007000D00101D0102000C00032Q001001033Q000500302B00030002000300302B00030004000300302B00030005000A00302B00030006000300302B00030007000F00101D0102000E00032Q001001033Q00042Q0010010400043Q001271010500103Q001271010600113Q001271010700123Q001271010800134Q00D600040004000100101D0103000100042Q0010010400023Q001271010500143Q001271010600154Q00D600040002000100101D0103000900042Q0010010400023Q001271010500163Q001271010600174Q00D600040002000100101D0103000C00042Q0010010400023Q001271010500183Q001271010600194Q00D600040002000100101D0103000E00040012FA0004001A4Q0058000500024Q004701040002000600043A012Q005800010012FA0009001B4Q0084000A000300072Q004701090002000B00043A012Q00560001000E24001C005600013Q00043A012Q00560001002030000E0001001D2Q00580010000D6Q000E0010000200068C010E005600013Q00043A012Q005600010012FA000E001E3Q0012E2000F001F6Q000E0002000100122Q000E001E3Q00122Q000F00206Q000E0002000100122Q000E00213Q00122Q000F001C3Q00122Q001000223Q00202Q00100010002300122Q001100243Q00202Q00120008000200202Q00130008000400202Q00140008000500202Q0015000800064Q001000156Q000E3Q00014Q000E00016Q000E00023Q0006140109003C0001000200043A012Q003C0001000614010400380001000200043A012Q003800012Q00573Q00017Q000F3Q00028Q0003043Q0066696E64030F3Q004F6E4469616C6F6752657175657374026Q00F03F03103Q00603452656379636C65206077282E2B2903053Q006D61746368031A3Q00656D6265645F646174617C6974656D5F74726173687C282E2B29030E3Q00796F752068617665202825642B29030A3Q0053656E645061636B6574027Q004003323Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C74726173680A6974656D5F74726173687C030D3Q007C0A6974656D5F636F756E747C034Q0003103Q004F6E436F6E736F6C654D652Q7361676503263Q006077282E2B29202Q6072656379636C65642C206030202Q6067656D73206561726E65642E2Q60013A3Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001002400013Q00043A012Q002400010020CC00013Q0004002030000100010002001271010300056Q00010003000200068C2Q01002400013Q00043A012Q002400012Q005900015Q00068C2Q01002400013Q00043A012Q002400010020CC00013Q00040020262Q010001000600122Q000300076Q0001000300024Q000100013Q00202Q00013Q000400202Q00010001000600122Q000300086Q0001000300024Q000100023Q00122Q000100093Q00122Q0002000A3Q00122Q0003000B6Q000400013Q00122Q0005000C6Q000600023Q00122Q0007000D6Q0003000300074Q0001000300014Q000100016Q000100023Q0020CC00013Q00010020300001000100020012710103000E6Q00010003000200068C2Q01003900013Q00043A012Q003900010020CC00013Q00040020300001000100020012710103000F6Q00010003000200068C2Q01003900013Q00043A012Q003900012Q005900015Q00068C2Q01003900013Q00043A012Q003900010012712Q0100014Q001A000100013Q0012712Q0100014Q001A000100024Q00052Q0100014Q0099000100024Q00573Q00017Q00033Q0003073Q006F7665726D736703183Q006065466173742060345472617368206032456E61626C656403193Q00606546617374206034547261736820606344697361626C656400104Q00369Q009Q009Q009Q003Q00018Q00013Q00064Q000C00013Q00043A012Q000C00010012FA3Q00013Q0012712Q0100024Q0044012Q0002000100043A012Q000F00010012FA3Q00013Q0012712Q0100034Q0044012Q000200012Q00573Q00017Q00053Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F667403163Q00616374696F6E7C696E7075740A7C746578747C2F465403083Q00746F2Q676C65465402113Q002659012Q00100001000100043A012Q00100001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102001000013Q00043A012Q001000010012FA000200054Q00620002000100012Q0005010200014Q0099000200024Q00573Q00017Q000F3Q00028Q0003043Q0066696E64030F3Q004F6E4469616C6F6752657175657374026Q00F03F030B3Q00607744726F7020282E2B2903023Q00666403073Q0064726F70506F7303053Q006D6174636803193Q00656D6265645F646174617C6974656D5F64726F707C282E2B29030E3Q00796F752068617665202825642B29030A3Q0053656E645061636B6574027Q004003303Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C64726F700A6974656D5F64726F707C030D3Q007C0A6974656D5F636F756E747C034Q0001253Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001002400013Q00043A012Q002400010020CC00013Q0004002030000100010002001271010300056Q00010003000200068C2Q01002400013Q00043A012Q002400010012FA000100063Q00068C2Q01002400013Q00043A012Q002400010020CC00013Q0004002030000100010008001271010300096Q0001000300020020CC00023Q00040020300002000200080012710104000A6Q0002000400022Q001A00025Q00120A000100073Q0012FA0001000B3Q0012710102000C3Q0012710103000D3Q0012FA000400073Q0012710105000E4Q005900065Q0012710107000F4Q006F0103000300072Q00EA0001000300012Q00052Q0100014Q0099000100024Q00573Q00017Q00043Q0003023Q00666403073Q006F7665726D736703173Q0060654661737420603444726F70206032456E61626C656403183Q0060654661737420603444726F7020606344697361626C6564000D3Q00127B3Q00019Q003Q00124Q00013Q00124Q00023Q00122Q000100013Q00062Q0001000A00013Q00043A012Q000A00010012712Q0100033Q00062D0001000B0001000100043A012Q000B00010012712Q0100044Q0044012Q000200012Q00573Q00017Q00043Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F666403163Q00616374696F6E7C696E7075740A7C746578747C2F464402113Q002659012Q00070001000100043A012Q00070001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102001000013Q00043A012Q001000012Q005900026Q00620002000100012Q0005010200014Q0099000200024Q00573Q00017Q00123Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F03393Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C605E4C6F6773204F7074696F6E737Q207C6C6566747C313433367C03463Q000A612Q645F696D6167655F62752Q746F6E7C62612Q6E65727C63616368652F696E746572666163652F6C617267652F62612Q6E65722E722Q7465787C6E6F666C6167733Q7C03123Q000A612Q645F7370616365727C736D612Q6C7C031C3Q000A612Q645F637573746F6D5F6D617267696E7C783A303B793A31307C03453Q000A612Q645F62752Q746F6E7C6C6F677370696E7C60397Q20526F756C652Q74652057682Q656C204C6F67739Q20207C6E6F666C6167737C307C033E3Q000A612Q645F62752Q746F6E7C6C6F6764726F707C60397Q2044726F2Q706564204C6F67739Q20207C6E6F666C6167737C307C03403Q000A612Q645F62752Q746F6E7C6C6F67632Q6C7C60397Q20436F2Q6C6563746564204C6F67739Q20202Q7C6E6F666C6167737C307C03413Q000A612Q645F62752Q746F6E7C6C6F6762752Q746F6E7C60397Q204265742042544B204C6F67739Q20202Q7C6E6F666C6167737C307C03403Q000A612Q645F62752Q746F6E7C6C6F6777696E317C60398Q2057696E2042544B204C6F67739Q20202Q7C6E6F666C6167737C307C03113Q000A612Q645F717569636B5F657869742Q7C03173Q000A612Q645F62752Q746F6E7C6261636B317C4261636B7C03173Q000A656E645F6469616C6F677C61687C43616E63656C2Q7C030B3Q0053656E645661726C697374001A4Q002E7Q00304Q0001000200304Q0003000400122Q000100063Q00122Q000200073Q00122Q000300083Q00122Q000400093Q00122Q0005000A3Q00122Q000600093Q00122Q0007000B3Q00122Q000800093Q00122Q0009000C3Q00122Q000A00093Q00122Q000B000D3Q00122Q000C00093Q00122Q000D000E3Q00122Q000E00083Q00122Q000F000F3Q00122Q001000103Q00122Q001100116Q00010001001100104Q0005000100122Q000100126Q00028Q0001000200016Q00017Q000F3Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F03333Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6032526F756C652Q7465204C6F67737C6C6566747C313433367C03123Q000A612Q645F7370616365727C736D612Q6C7C03283Q000A612Q645F62752Q746F6E7C72657365747370696E7C603452657365747C6E6F666C6167737C307C03013Q000A03073Q004C6F675370696E034Q0003113Q000A612Q645F717569636B5F657869742Q7C031C3Q000A612Q645F62752Q746F6E7C6B6F6E746F6C6F646F6E7C4261636B7C031F3Q000A656E645F6469616C6F677C776F726C645F7370696E7C43616E63656C2Q7C030B3Q0053656E645661726C69737400134Q00347Q00304Q0001000200304Q0003000400122Q000100063Q00122Q000200073Q00122Q000300083Q00122Q000400093Q00122Q0005000A3Q00122Q0006000B3Q00122Q000700073Q00122Q0008000C3Q00122Q0009000D3Q00122Q000A000E6Q00010001000A00104Q0005000100122Q0001000F6Q00028Q0001000200016Q00017Q000F3Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F03323Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603244726F2Q706564204C6F67737C6C6566747C313433367C03123Q000A612Q645F7370616365727C736D612Q6C7C03283Q000A612Q645F62752Q746F6E7C726573657464726F707C603452657365747C6E6F666C6167737C307C03013Q000A03073Q004C6F6744726F70034Q0003113Q000A612Q645F717569636B5F657869742Q7C031C3Q000A612Q645F62752Q746F6E7C6B6F6E746F6C6F646F6E7C4261636B7C031F3Q000A656E645F6469616C6F677C776F726C645F7370696E7C43616E63656C2Q7C030B3Q0053656E645661726C69737400134Q00347Q00304Q0001000200304Q0003000400122Q000100063Q00122Q000200073Q00122Q000300083Q00122Q000400093Q00122Q0005000A3Q00122Q0006000B3Q00122Q000700073Q00122Q0008000C3Q00122Q0009000D3Q00122Q000A000E6Q00010001000A00104Q0005000100122Q0001000F6Q00028Q0001000200016Q00017Q000F3Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F03343Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6032436F2Q6C6563746564204C6F67737C6C6566747C313433367C03123Q000A612Q645F7370616365727C736D612Q6C7C03283Q000A612Q645F62752Q746F6E7C7265736574636F2Q6C7C603452657365747C6E6F666C6167737C307C03013Q000A030A3Q004C6F67436F2Q6C656374034Q0003113Q000A612Q645F717569636B5F657869742Q7C031C3Q000A612Q645F62752Q746F6E7C6B6F6E746F6C6F646F6E7C4261636B7C031F3Q000A656E645F6469616C6F677C776F726C645F7370696E7C43616E63656C2Q7C030B3Q0053656E645661726C69737400134Q00347Q00304Q0001000200304Q0003000400122Q000100063Q00122Q000200073Q00122Q000300083Q00122Q000400093Q00122Q0005000A3Q00122Q0006000B3Q00122Q000700073Q00122Q0008000C3Q00122Q0009000D3Q00122Q000A000E6Q00010001000A00104Q0005000100122Q0001000F6Q00028Q0001000200016Q00017Q000F3Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F032F3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603242657473204C6F67737C6C6566747C313433367C03123Q000A612Q645F7370616365727C736D612Q6C7C03283Q000A612Q645F62752Q746F6E7C7265736574636F2Q6C7C603452657365747C6E6F666C6167737C307C03013Q000A03063Q004C6F67424554034Q0003113Q000A612Q645F717569636B5F657869742Q7C031C3Q000A612Q645F62752Q746F6E7C6B6F6E746F6C6F646F6E7C4261636B7C031F3Q000A656E645F6469616C6F677C776F726C645F7370696E7C43616E63656C2Q7C030B3Q0053656E645661726C69737400134Q00347Q00304Q0001000200304Q0003000400122Q000100063Q00122Q000200073Q00122Q000300083Q00122Q000400093Q00122Q0005000A3Q00122Q0006000B3Q00122Q000700073Q00122Q0008000C3Q00122Q0009000D3Q00122Q000A000E6Q00010001000A00104Q0005000100122Q0001000F6Q00028Q0001000200016Q00017Q000F3Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F032F3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603257696E73204C6F67737C6C6566747C313433367C03123Q000A612Q645F7370616365727C736D612Q6C7C03283Q000A612Q645F62752Q746F6E7C7265736574636F2Q6C7C603452657365747C6E6F666C6167737C307C03013Q000A03063Q004C6F6757494E034Q0003113Q000A612Q645F717569636B5F657869742Q7C031C3Q000A612Q645F62752Q746F6E7C6B6F6E746F6C6F646F6E7C4261636B7C031F3Q000A656E645F6469616C6F677C776F726C645F7370696E7C43616E63656C2Q7C030B3Q0053656E645661726C69737400134Q00347Q00304Q0001000200304Q0003000400122Q000100063Q00122Q000200073Q00122Q000300083Q00122Q000400093Q00122Q0005000A3Q00122Q0006000B3Q00122Q000700073Q00122Q0008000C3Q00122Q0009000D3Q00122Q000A000E6Q00010001000A00104Q0005000100122Q0001000F6Q00028Q0001000200016Q00017Q001C3Q0003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F6C6F6703183Q00616374696F6E7C696E7075740A7C746578747C2F6C6F677303073Q006C6F676D656E7503153Q0062752Q746F6E436C69636B65647C6C6F677370696E03023Q006C7303153Q0062752Q746F6E436C69636B65647C6C6F6764726F7003023Q006C6403143Q0062752Q746F6E436C69636B65647C6C6F67632Q6C03023Q006C6303173Q0062752Q746F6E436C69636B65647C6C6F6762752Q746F6E03043Q0062742Q6B03153Q0062752Q746F6E436C69636B65647C6C6F6777696E3103053Q0062742Q6B3103153Q0062752Q746F6E436C69636B65647C4C6F672Q43545603173Q0062752Q746F6E436C69636B65647C72657365747370696E03073Q004C6F675370696E034Q0003073Q006F7665726D7367031E3Q00526F756C652Q7465204C6F67732048617320422Q656E206034526573657403173Q0062752Q746F6E436C69636B65647C726573657464726F7003073Q004C6F6744726F70031D3Q0044726F2Q706564204C6F67732048617320422Q656E206034526573657403173Q0062752Q746F6E436C69636B65647C7265736574636F2Q6C030A3Q004C6F67436F2Q6C656374031F3Q00436F2Q6C6563746564204C6F67732048617320422Q656E206034526573657403063Q004C6F6742455403183Q0062752Q746F6E436C69636B65647C6B6F6E746F6C6F646F6E02873Q002030000200010001001271010400026Q00020004000200062D0002000A0001000100043A012Q000A0001002030000200010001001271010400036Q00020004000200068C0102000F00013Q00043A012Q000F00010012FA000200044Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q00860001002030000200010001001271010400056Q00020004000200068C0102001900013Q00043A012Q001900010012FA000200064Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q00860001002030000200010001001271010400076Q00020004000200068C0102002300013Q00043A012Q002300010012FA000200084Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q00860001002030000200010001001271010400096Q00020004000200068C0102002D00013Q00043A012Q002D00010012FA0002000A4Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q008600010020300002000100010012710104000B6Q00020004000200068C0102003700013Q00043A012Q003700010012FA0002000C4Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q008600010020300002000100010012710104000D6Q00020004000200068C0102004100013Q00043A012Q004100010012FA0002000E4Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q008600010020300002000100010012710104000F6Q00020004000200068C0102004B00013Q00043A012Q004B00010012FA000200044Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q00860001002030000200010001001271010400106Q00020004000200068C0102005800013Q00043A012Q00580001001271010200123Q0012A1010200113Q00122Q000200133Q00122Q000300146Q0002000200014Q000200016Q000200023Q00044Q00860001002030000200010001001271010400156Q00020004000200068C0102006500013Q00043A012Q00650001001271010200123Q0012A1010200163Q00122Q000200133Q00122Q000300176Q0002000200014Q000200016Q000200023Q00044Q00860001002030000200010001001271010400186Q00020004000200068C0102007200013Q00043A012Q00720001001271010200123Q0012A1010200193Q00122Q000200133Q00122Q0003001A6Q0002000200014Q000200016Q000200023Q00044Q00860001002030000200010001001271010400186Q00020004000200068C0102007D00013Q00043A012Q007D0001001271010200123Q0012200002001B3Q00122Q000200133Q00122Q0003001A6Q00020002000100044Q008600010020300002000100010012710104001C6Q00020004000200068C0102008600013Q00043A012Q008600010012FA000200044Q00620002000100012Q0005010200014Q0099000200024Q00573Q00017Q000F3Q00028Q0003103Q004F6E5061727469636C65452Q66656374026Q00F03F025Q00805C40027Q004003083Q004765744C6F63616C03053Q00706F735F78026Q00244003053Q00706F735F79026Q002E40026Q000840026Q00104003053Q006E65746964026Q00F0BF030B3Q0053656E645661726C69737400154Q0010016Q00302B3Q0001000200302B3Q000300042Q00102Q0100023Q0012FA000200064Q00960102000100020020CC0002000200070020790102000200080012FA000300064Q00960103000100020020CC00030003000900207901030003000A2Q00D600010002000100101D012Q000500010030403Q000B000100304Q000C000100304Q000D000E00122Q0001000F6Q00028Q0001000200016Q00019Q002Q0004063Q00068901043Q000100032Q00588Q00583Q00034Q00583Q00024Q0099000400024Q00573Q00013Q00013Q00173Q00027Q004003043Q0066696E6403143Q00616374696F6E7C696E7075740A7C746578747C2F03053Q00752Q70657203103Q0062752Q746F6E436C69636B65647C2Q6303023Q00617003013Q003103023Q00616203013Q003203013Q003303023Q005F470100030A3Q0053656E645061636B657403123Q00616374696F6E7C696E7075740A746578747C030D3Q004F6E546578744F7665726C617903013Q00202Q0103063Q0069706169727303023Q00616B03243Q0060775B606320576176652050726F78792060775D2060334160355560235460314F20606303063Q00737472696E672Q033Q0073756203183Q00205752454E43482060234D4F44452060344F2Q4620606321027A3Q002659012Q00790001000100043A012Q0079000100203000020001000200129C010400036Q00058Q0004000400054Q00020004000200062Q000200250001000100043A012Q0025000100203000020001000200126E010400036Q00055Q00202Q0005000500044Q0005000200024Q0004000400054Q00020004000200062Q000200250001000100043A012Q00250001002030000200010002001271010400054Q005900055Q0026590105001A0001000600043A012Q001A0001001271010500073Q00062D000500210001000100043A012Q002100012Q005900055Q002659010500200001000800043A012Q00200001001271010500093Q00062D000500210001000100043A012Q002100010012710105000A4Q006F0104000400054Q00020004000200068C0102007900013Q00043A012Q007900010012FA0002000B4Q005900036Q008400020002000300068C0102003C00013Q00043A012Q003C00010012FA0002000B4Q003100035Q00202Q00020003000C00122Q0002000D3Q00122Q000300013Q00122Q0004000E6Q000500016Q0004000400054Q00020004000100122Q0002000F6Q000300016Q00020002000100122Q0002000F6Q000300013Q00122Q000400106Q0003000300044Q00020002000100044Q007700010012FA0002000B4Q001501035Q00202Q00020003001100122Q0002000D3Q00122Q000300013Q00122Q0004000E6Q000500026Q0004000400054Q00020004000100122Q0002000F6Q000300026Q00020002000100122Q0002000F6Q000300023Q00122Q000400106Q0003000300044Q00020002000100122Q000200126Q000300033Q00122Q000400063Q00122Q000500133Q00122Q000600086Q0003000300012Q004701020002000400043A012Q007500012Q005900075Q00063F000600750001000700043A012Q007500010012FA0007000B4Q008400070007000600068C0107007500013Q00043A012Q007500010012FA0007000B3Q00202600070006000C00122Q000700143Q00122Q000800153Q00202Q00080008000400202Q00090006001600122Q000B00016Q0009000B6Q00083Q000200122Q000900176Q00070007000900122Q0008000D3Q00122Q000900013Q00122Q000A000E6Q000B00076Q000A000A000B4Q0008000A000100122Q0008000F6Q000900076Q00080002000100122Q0008000F6Q000900073Q00122Q000A00106Q00090009000A4Q000800020001000614010200550001000200043A012Q005500012Q0005010200014Q0099000200024Q00573Q00017Q001A3Q0003043Q0066696E6403143Q00616374696F6E7C7772656E63680A7C6E6574696403063Q00737472696E6703053Q006D61746368031A3Q00616374696F6E7C7772656E63680A7C6E657469647C2825642B2903083Q00746F6E756D62657203023Q00617003043Q0070752Q6C03063Q0050752Q6C656403083Q00603250752Q6C656403023Q00616203093Q00776F726C645F62616E03063Q0042612Q6E656403093Q00603442612Q6E696E6703023Q00616B03043Q006B69636B03063Q004B69636B656403093Q00606F4B69636B696E6703053Q007061697273030A3Q00476574506C617965727303053Q006E65746964030A3Q0053656E645061636B6574027Q0040032D3Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C706F7075700A6E657449447C03103Q007C0A62752Q746F6E436C69636B65647C03093Q0052756E54687265616402483Q002030000200010001001271010400026Q00020004000200068C0102004700013Q00043A012Q004700010012FA000200033Q0020CC0002000200042Q0058000300013Q001271010400056Q0002000400020012FA000300064Q0058000400024Q00C60003000200022Q0082010400063Q0012FA000700073Q00068C0107001700013Q00043A012Q00170001001271010700083Q001292010800093Q00122Q0006000A6Q000500086Q000400073Q00044Q002A00010012FA0007000B3Q00068C0107002000013Q00043A012Q002000010012710107000C3Q0012920108000D3Q00122Q0006000E6Q000500086Q000400073Q00044Q002A00010012FA0007000F3Q00068C0107002900013Q00043A012Q00290001001271010700103Q001292010800113Q00122Q000600126Q000500086Q000400073Q00044Q002A00012Q00573Q00013Q0012FA000700133Q0012FA000800144Q00DA000800014Q00AC00073Q000900043A012Q004400010020CC000C000B0015000668000C00430001000300043A012Q004300010012FA000C00163Q001211000D00173Q00122Q000E00186Q000F00023Q00122Q001000196Q001100046Q000E000E00114Q000C000E000100122Q000C001A3Q000689010D3Q000100042Q00583Q000B4Q00583Q00064Q00583Q00044Q00583Q00054Q0044010C000200012Q0005010C00014Q0099000C00024Q005A000A5Q0006140107002F0001000200043A012Q002F00012Q005A00026Q00573Q00013Q00013Q001B3Q0003063Q006474315F786403043Q006E616D6503043Q006773756203023Q00602E034Q00030A3Q0053656E645061636B6574027Q004003273Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2003013Q002003053Q00536C2Q6570025Q00408F4003123Q00616374696F6E7C696E7075740A746578747C03043Q0070752Q6C2Q033Q0060775B03093Q007370616D746578747303113Q006030286E756B6529286576696C2960775D2Q033Q005B603403063Q00737472696E6703053Q00752Q706572030F3Q006030286E756B6529286576696C295D030D3Q004F6E546578744F7665726C617903153Q0060775B606320576176652050726F78792060775D202Q033Q0020603903063Q002060775B602303053Q006E657469642Q033Q0060775D03043Q0060775D2000463Q0012163Q00018Q000100019Q0000206Q000200206Q000300122Q000200043Q00122Q000300058Q0003000200122Q000100063Q00122Q000200073Q00122Q000300086Q000400013Q00122Q000500096Q00065Q00202Q0006000600024Q0003000300064Q00010003000100122Q0001000A3Q00122Q0002000B6Q00010002000100122Q000100063Q00122Q000200073Q00122Q0003000C6Q000400023Q00262Q000400230001000D00043A012Q002300010012710104000E3Q0012720105000F3Q00122Q000600096Q00075Q00202Q00070007000200122Q000800106Q00040004000800062Q0004002D0001000100043A012Q002D0001001271010400113Q0012FA000500123Q0020CC0005000500132Q0059000600034Q00C6000500020002001271010600094Q005900075Q0020CC000700070002001271010800144Q006F0104000400082Q006F0103000300042Q000F00010003000100122Q000100153Q00122Q000200166Q000300013Q00122Q000400176Q00055Q00122Q000600186Q00075Q00202Q00070007001900122Q0008001A4Q006F0102000200082Q00442Q01000200010012FA000100153Q001271010200164Q0059000300013Q001271010400174Q005800055Q001271010600184Q005900075Q0020CC0007000700190012710108001B4Q006F0102000200082Q00442Q01000200012Q00573Q00017Q000A3Q0003013Q0062026Q00594003013Q006103043Q006D61746803053Q00666C2Q6F72025Q0088C34003013Q0063024Q0080842E4103013Q006503093Q0052756E54687265616401173Q0020582Q013Q000200120A000100013Q0012FA000100043Q0020CC00010001000500205801023Q00060020FB0002000200022Q00C600010002000200120A000100033Q0012FA000100043Q0020CC00010001000500205801023Q00080020FB0002000200062Q00C600010002000200120A000100073Q0012FA000100043Q0020CC0001000100050020FB00023Q00082Q00C600010002000200120A000100093Q0012FA0001000A3Q00029C00026Q00442Q01000200012Q00573Q00013Q00013Q001A3Q0003053Q00536C2Q6570026Q00694003013Q0065028Q00030A3Q0053656E645061636B6574027Q004003423Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C64726F700A6974656D5F64726F707C2Q312Q35307C0A6974656D5F636F756E747C034Q0003013Q006303043Q006D61746803053Q00666C2Q6F72030C3Q004765744974656D436F756E74025Q0014BC4003433Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C696E666F5F626F780A62752Q746F6E436C69636B65647C6D616B655F626C7565676C026Q00594003413Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C64726F700A6974656D5F64726F707C37312Q387C0A6974656D5F636F756E747C03013Q0061025Q00109C4003043Q0074797065026Q00244003083Q00696E745F64617461030D3Q0053656E645061636B657452617703413Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C64726F700A6974656D5F64726F707C313739367C0A6974656D5F636F756E747C03013Q0062025Q00406E4003403Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C64726F700A6974656D5F64726F707C3234327C0A6974656D5F636F756E747C00723Q001261012Q00013Q00122Q000100028Q0002000100124Q00033Q000E2Q0004001000013Q00043A012Q001000010012FA3Q00053Q0012B5000100063Q00122Q000200073Q00122Q000300033Q00122Q000400086Q0002000200046Q000200010012FA3Q00013Q0012712Q0100024Q0044012Q000200010012FA3Q00093Q000E390104003000013Q00043A012Q003000010012FA3Q000A3Q002084014Q000B00122Q0001000C3Q00122Q0002000D6Q000100029Q00000200122Q0001000A3Q00202Q00010001000B00122Q000200096Q00010002000200064Q00260001000100043A012Q002600010012FA3Q00053Q0012132Q0100063Q00122Q0002000E8Q0002000100124Q00013Q00122Q0001000F8Q000200010012FA3Q00053Q0012B5000100063Q00122Q000200103Q00122Q000300093Q00122Q000400086Q0002000200046Q000200010012FA3Q00013Q0012712Q0100024Q0044012Q000200010012FA3Q00113Q000E390104005200013Q00043A012Q005200010012FA3Q000A3Q002084014Q000B00122Q0001000C3Q00122Q000200126Q000100029Q00000200122Q0001000A3Q00202Q00010001000B00122Q000200116Q00010002000200064Q00480001000100043A012Q004800012Q0010016Q0030633Q0013001400304Q0015000D00122Q000100166Q00028Q00010002000100122Q000100013Q00122Q0002000F6Q0001000200010012FA3Q00053Q0012B5000100063Q00122Q000200173Q00122Q000300113Q00122Q000400086Q0002000200046Q000200010012FA3Q00013Q0012712Q0100024Q0044012Q000200010012FA3Q00183Q000E390104007100013Q00043A012Q007100010012FA3Q000A3Q002084014Q000B00122Q0001000C3Q00122Q000200196Q000100029Q00000200122Q0001000A3Q00202Q00010001000B00122Q000200186Q00010002000200064Q006A0001000100043A012Q006A00012Q0010016Q0030633Q0013001400304Q0015001200122Q000100166Q00028Q00010002000100122Q000100013Q00122Q0002000F6Q0001000200010012FA3Q00053Q0012B5000100063Q00122Q0002001A3Q00122Q000300183Q00122Q000400086Q0002000200046Q000200012Q00573Q00017Q000D3Q00027Q004003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F63642003173Q00616374696F6E7C696E7075740A7C746578747C2F43442003063Q00737472696E6703053Q006D61746368031C3Q00616374696F6E7C696E7075740A7C746578747C2F6364202825642B29031C3Q00616374696F6E7C696E7075740A7C746578747C2F4344202825642B29030C3Q00202825642B252E3F25642A2903083Q00746F6E756D62657203043Q0044726F70030B3Q0070726F63652Q7344726F7003073Q0044726F2Q706564023D3Q002659012Q003C0001000100043A012Q003C0001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102003C00013Q00043A012Q003C00010012FA000200053Q0020670002000200064Q000300013Q00122Q000400076Q00020004000200062Q000200180001000100043A012Q001800010012FA000200053Q0020CC0002000200062Q0058000300013Q001271010400086Q0002000400020012FA000300053Q00208D0003000300064Q000400013Q00122Q000500036Q000600023Q00122Q000700096Q0005000500074Q00030005000200062Q0003002A0001000100043A012Q002A00010012FA000300053Q0020870103000300064Q000400013Q00122Q000500046Q000600023Q00122Q000700096Q0005000500074Q00030005000200068C0103003300013Q00043A012Q003300010012FA0004000A4Q008D010500026Q00040002000200122Q0005000A6Q000600036Q0005000200024Q0002000400050012FA0004000B4Q0097010500026Q00040002000100122Q0004000C6Q000500023Q00122Q0006000D6Q0004000600014Q000400016Q000400024Q00573Q00017Q00013Q0003093Q0052756E54687265616402063Q0012FA000200013Q00068901033Q000100022Q00588Q00583Q00014Q00440102000200012Q00573Q00013Q00013Q001E3Q0003043Q006D61746803053Q00666C2Q6F72024Q0080842E41025Q0088C340026Q005940028Q0003133Q00206062426C61636B2047656D204C6F636B6030034Q0003013Q002003123Q00206065426C75652047656D204C6F636B603003113Q002060314469616D6F6E64204C6F636B6030030F3Q00206039576F726C64204C6F636B603003043Q00677375622Q033Q005E257303073Q006F7665726D736703023Q0060322Q033Q00206030030A3Q0053656E645061636B6574027Q004003123Q00616374696F6E7C696E7075740A746578747C03073Q00746578746574632Q033Q0020607703073Q004C6F6744726F7003203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203023Q006F7303043Q006461746503053Q0025483A254D030B3Q0060775D20596F75277665202Q033Q00206035030B3Q007C6C6566747C3234327C0A005B3Q0012CA3Q00013Q00206Q00024Q00015Q00202Q0001000100036Q0002000200122Q000100013Q00202Q0001000100024Q00025Q00202Q00020002000300202Q0002000200042Q00C60001000200020012FA000200013Q0020CC0002000200022Q005900035Q0020580103000300040020FB0003000300052Q00C60002000200022Q005900035Q00205801030003000500265B3Q001A0001000600043A012Q001A00012Q005800045Q001271010500074Q006F01040004000500062D0004001B0001000100043A012Q001B0001001271010400083Q00265B000100230001000600043A012Q00230001001271010500094Q0058000600013Q0012710107000A4Q006F01050005000700062D000500240001000100043A012Q00240001001271010500083Q00265B0002002C0001000600043A012Q002C0001001271010600094Q0058000700023Q0012710108000B4Q006F01060006000800062D0006002D0001000100043A012Q002D0001001271010600083Q00265B000300350001000600043A012Q00350001001271010700094Q0058000800033Q0012710109000C4Q006F01070007000900062D000700360001000100043A012Q00360001001271010700084Q006F01040004000700203000050004000D0012710107000E3Q001271010800086Q0005000800022Q0058000400053Q0012FA0005000F3Q001271010600104Q0059000700013Q001271010800114Q0058000900044Q006F0106000600092Q00A400050002000100122Q000500123Q00122Q000600133Q00122Q000700143Q00122Q000800153Q00122Q000900166Q000A00013Q00122Q000B00096Q000C00046Q00070007000C2Q00EA0005000700010012FA000500173Q001271010600183Q0012FA000700193Q0020CC00070007001A0012710108001B4Q00C60007000200020012710108001C4Q0059000900013Q001271010A001D4Q0058000B00043Q001271010C001E4Q006F01050005000C00120A000500174Q00573Q00017Q00013Q0003093Q0052756E546872656164040A3Q0012FA000400013Q00068901053Q000100042Q00588Q00583Q00014Q00583Q00024Q00583Q00034Q00440104000200012Q0005010400014Q0099000400024Q00573Q00013Q00013Q001F3Q0003053Q00536C2Q6570026Q00594003043Q006D61746803053Q00666C2Q6F72030C3Q004765744974656D436F756E7403073Q006F7665726D7367030F3Q0060394E6F7420656E6F756768206065030E3Q0073206039746F2064726F7060772E030A3Q0053656E645061636B6574027Q004003123Q00616374696F6E7C696E7075740A746578747C03073Q0074657874657463030F3Q002060394E6F7420656E6F7567682060034Q00030C3Q00603244726F2Q70656420607703083Q00746F737472696E6703013Q006003013Q002003013Q0073030D3Q0020603244726F2Q70656420607703023Q00206003303Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C64726F700A6974656D5F64726F707C030D3Q007C0A6974656D5F636F756E747C03073Q004C6F6744726F7003203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203023Q006F7303043Q006461746503053Q0025483A254D03153Q0060775D20596F752776652044726F2Q70656420603503063Q007C6C6566747C03023Q007C0A005D3Q00127A012Q00013Q00122Q000100028Q0002000100124Q00033Q00206Q000400122Q000100056Q00028Q000100029Q00000200122Q000100033Q00202Q0001000100044Q000200016Q00010002000200064Q00210001000100043A012Q002100010012FA000100063Q00129E010200076Q000300023Q00122Q000400086Q0002000200044Q00010002000100122Q000100093Q00122Q0002000A3Q00122Q0003000B3Q00122Q0004000C3Q00122Q0005000D4Q0059000600033Q0012710107000E4Q0059000800023Q001271010900084Q006F0103000300092Q00EA00010003000100043A012Q005C00010012FA000100013Q001271010200024Q00442Q01000200010012FA000100063Q0012710102000F3Q0012FA000300103Q0012FA000400033Q0020CC0004000400042Q0059000500014Q000A010400054Q00C500033Q0002001271010400114Q0059000500033Q00129E010600126Q000700023Q00122Q000800136Q0002000200084Q00010002000100122Q000100093Q00122Q0002000A3Q00122Q0003000B3Q00122Q0004000C3Q00122Q000500143Q001251010600103Q00122Q000700033Q00202Q0007000700044Q000800016Q000700086Q00063Q000200122Q000700156Q000800036Q000900023Q00122Q000A00134Q006F01030003000A2Q00482Q010003000100122Q000100093Q00122Q0002000A3Q00122Q000300166Q00045Q00122Q000500176Q000600016Q0003000300064Q00010003000100122Q000100183Q001271010200193Q0012350103001A3Q00202Q00030003001B00122Q0004001C6Q00030002000200122Q0004001D6Q000500013Q00122Q000600156Q000700036Q000800023Q00122Q0009001E4Q0059000A5Q001271010B001F4Q006F2Q010001000B00120A000100184Q00573Q00017Q000F3Q00027Q004003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F64772003173Q00616374696F6E7C696E7075740A7C746578747C2F44572003173Q00616374696F6E7C696E7075740A7C746578747C2F776C2003173Q00616374696F6E7C696E7075740A7C746578747C2F574C2003063Q00737472696E6703053Q006D6174636803223Q00616374696F6E7C696E7075740A7C746578747C2F5B64775D5B776C5D202825642B2903223Q00616374696F6E7C696E7075740A7C746578747C2F5B44575D5B574C5D202825642B29031D3Q00616374696F6E7C696E7075740A7C746578747C2F5B64775D5B776C5D20030C3Q00202825642B252E3F25642A29031D3Q00616374696F6E7C696E7075740A7C746578747C2F5B44575D5B574C5D2003083Q00746F6E756D62657203093Q0052756E54687265616402453Q002659012Q00440001000100043A012Q00440001002030000200010002001271010400036Q00020004000200062D000200160001000100043A012Q00160001002030000200010002001271010400046Q00020004000200062D000200160001000100043A012Q00160001002030000200010002001271010400056Q00020004000200062D000200160001000100043A012Q00160001002030000200010002001271010400066Q00020004000200068C0102004400013Q00043A012Q004400010012FA000200073Q0020670002000200084Q000300013Q00122Q000400096Q00020004000200062Q000200220001000100043A012Q002200010012FA000200073Q0020CC0002000200082Q0058000300013Q0012710104000A6Q0002000400020012FA000300073Q00208D0003000300084Q000400013Q00122Q0005000B6Q000600023Q00122Q0007000C6Q0005000500074Q00030005000200062Q000300340001000100043A012Q003400010012FA000300073Q0020870103000300084Q000400013Q00122Q0005000D6Q000600023Q00122Q0007000C6Q0005000500074Q00030005000200068C0103003D00013Q00043A012Q003D00010012FA0004000E4Q008D010500026Q00040002000200122Q0005000E6Q000600036Q0005000200024Q0002000400050012FA0004000F3Q00068901053Q000100012Q00583Q00024Q00440104000200012Q0005010400014Q0099000400024Q005A00026Q00573Q00013Q00013Q000E3Q0003043Q006D61746803053Q00666C2Q6F72030C3Q004765744974656D436F756E74025Q00406E4003043Q0074797065026Q00244003083Q00696E745F64617461025Q00109C40030D3Q0053656E645061636B657452617703053Q00536C2Q6570026Q00594003083Q0064726F704974656D030A3Q00576F726C64204C6F636B03013Q003900203Q0012C23Q00013Q00206Q000200122Q000100033Q00122Q000200046Q000100029Q00000200122Q000100013Q00202Q0001000100024Q00028Q00010002000200064Q00150001000100043A012Q001500012Q0010014Q00020030633Q0005000600304Q0007000800122Q000100096Q00028Q00010002000100122Q0001000A3Q00122Q0002000B6Q0001000200010012FA3Q000A3Q0012522Q01000B8Q0002000100124Q000C3Q00122Q000100046Q00025Q00122Q0003000D3Q00122Q0004000E8Q00049Q008Q00017Q000F3Q00027Q004003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F2Q642003173Q00616374696F6E7C696E7075740A7C746578747C2F2Q442003173Q00616374696F6E7C696E7075740A7C746578747C2F646C2003173Q00616374696F6E7C696E7075740A7C746578747C2F444C2003063Q00737472696E6703053Q006D6174636803223Q00616374696F6E7C696E7075740A7C746578747C2F5B2Q645D5B646C5D202825642B2903223Q00616374696F6E7C696E7075740A7C746578747C2F5B2Q445D5B444C5D202825642B29031D3Q00616374696F6E7C696E7075740A7C746578747C2F5B2Q645D5B646C5D20030C3Q00202825642B252E3F25642A29031D3Q00616374696F6E7C696E7075740A7C746578747C2F5B2Q445D5B444C5D2003083Q00746F6E756D62657203093Q0052756E54687265616402453Q002659012Q00440001000100043A012Q00440001002030000200010002001271010400036Q00020004000200062D000200160001000100043A012Q00160001002030000200010002001271010400046Q00020004000200062D000200160001000100043A012Q00160001002030000200010002001271010400056Q00020004000200062D000200160001000100043A012Q00160001002030000200010002001271010400066Q00020004000200068C0102004400013Q00043A012Q004400010012FA000200073Q0020670002000200084Q000300013Q00122Q000400096Q00020004000200062Q000200220001000100043A012Q002200010012FA000200073Q0020CC0002000200082Q0058000300013Q0012710104000A6Q0002000400020012FA000300073Q00208D0003000300084Q000400013Q00122Q0005000B6Q000600023Q00122Q0007000C6Q0005000500074Q00030005000200062Q000300340001000100043A012Q003400010012FA000300073Q0020870103000300084Q000400013Q00122Q0005000D6Q000600023Q00122Q0007000C6Q0005000500074Q00030005000200068C0103003D00013Q00043A012Q003D00010012FA0004000E4Q008D010500026Q00040002000200122Q0005000E6Q000600036Q0005000200024Q0002000400050012FA0004000F3Q00068901053Q000100012Q00583Q00024Q00440104000200012Q0005010400014Q0099000400024Q005A00026Q00573Q00013Q00013Q000E3Q0003043Q006D61746803053Q00666C2Q6F72030C3Q004765744974656D436F756E74025Q00109C4003043Q0074797065026Q00244003083Q00696E745F64617461025Q0014BC40030D3Q0053656E645061636B657452617703053Q00536C2Q6570026Q00594003083Q0064726F704974656D030C3Q004469616D6F6E64204C6F636B03013Q006300203Q0012C23Q00013Q00206Q000200122Q000100033Q00122Q000200046Q000100029Q00000200122Q000100013Q00202Q0001000100024Q00028Q00010002000200064Q00150001000100043A012Q001500012Q0010014Q00020030633Q0005000600304Q0007000800122Q000100096Q00028Q00010002000100122Q0001000A3Q00122Q0002000B6Q0001000200010012FA3Q000A3Q0012522Q01000B8Q0002000100124Q000C3Q00122Q000100046Q00025Q00122Q0003000D3Q00122Q0004000E8Q00049Q008Q00017Q000F3Q00027Q004003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F64622003173Q00616374696F6E7C696E7075740A7C746578747C2F44422003183Q00616374696F6E7C696E7075740A7C746578747C2F62676C2003183Q00616374696F6E7C696E7075740A7C746578747C2F42474C2003063Q00737472696E6703053Q006D6174636803233Q00616374696F6E7C696E7075740A7C746578747C2F5B64625D5B62676C5D202825642B2903233Q00616374696F6E7C696E7075740A7C746578747C2F5B44425D5B42474C5D202825642B29031E3Q00616374696F6E7C696E7075740A7C746578747C2F5B64625D5B62676C5D20030C3Q00202825642B252E3F25642A29031E3Q00616374696F6E7C696E7075740A7C746578747C2F5B44425D5B42474C5D2003083Q00746F6E756D62657203093Q0052756E54687265616402453Q002659012Q00440001000100043A012Q00440001002030000200010002001271010400036Q00020004000200062D000200160001000100043A012Q00160001002030000200010002001271010400046Q00020004000200062D000200160001000100043A012Q00160001002030000200010002001271010400056Q00020004000200062D000200160001000100043A012Q00160001002030000200010002001271010400066Q00020004000200068C0102004400013Q00043A012Q004400010012FA000200073Q0020670002000200084Q000300013Q00122Q000400096Q00020004000200062Q000200220001000100043A012Q002200010012FA000200073Q0020CC0002000200082Q0058000300013Q0012710104000A6Q0002000400020012FA000300073Q00208D0003000300084Q000400013Q00122Q0005000B6Q000600023Q00122Q0007000C6Q0005000500074Q00030005000200062Q000300340001000100043A012Q003400010012FA000300073Q0020870103000300084Q000400013Q00122Q0005000D6Q000600023Q00122Q0007000C6Q0005000500074Q00030005000200068C0103003D00013Q00043A012Q003D00010012FA0004000E4Q008D010500026Q00040002000200122Q0005000E6Q000600036Q0005000200024Q0002000400050012FA0004000F3Q00068901053Q000100012Q00583Q00024Q00440104000200012Q0005010400014Q0099000400024Q005A00026Q00573Q00013Q00013Q000E3Q00026Q00F03F026Q00084003043Q006D61746803053Q00666C2Q6F72030C3Q004765744974656D436F756E74025Q0014BC40030A3Q0053656E645061636B6574027Q004003433Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C696E666F5F626F780A62752Q746F6E436C69636B65647C6D616B655F626C7565676C03053Q00536C2Q6570026Q00594003083Q0064726F704974656D030D3Q00426C75652047656D204C6F636B03013Q006500233Q001271012Q00013Q0012712Q0100023Q001271010200013Q00040D012Q001800010012FA000400033Q00204B00040004000400122Q000500053Q00122Q000600066Q000500066Q00043Q000200122Q000500033Q00202Q0005000500044Q00068Q00050002000200062Q000400170001000500043A012Q001700010012FA000400073Q001213010500083Q00122Q000600096Q00040006000100122Q0004000A3Q00122Q0005000B6Q0004000200010004513Q000400010012FA3Q000A3Q0012522Q01000B8Q0002000100124Q000C3Q00122Q000100066Q00025Q00122Q0003000D3Q00122Q0004000E8Q00049Q008Q00017Q00163Q00027Q004003043Q0066696E6403183Q00616374696F6E7C696E7075740A7C746578747C2F642Q622003183Q00616374696F6E7C696E7075740A7C746578747C2F442Q422003183Q00616374696F6E7C696E7075740A7C746578747C2F64626C2003183Q00616374696F6E7C696E7075740A7C746578747C2F44424C2003183Q00616374696F6E7C696E7075740A7C746578747C2F626C632003183Q00616374696F6E7C696E7075740A7C746578747C2F424C432003063Q00737472696E6703053Q006D61746368031D3Q00616374696F6E7C696E7075740A7C746578747C2F642Q62202825642B29031D3Q00616374696F6E7C696E7075740A7C746578747C2F442Q42202825642B29031D3Q00616374696F6E7C696E7075740A7C746578747C2F64626C202825642B29031D3Q00616374696F6E7C696E7075740A7C746578747C2F44424C202825642B29031D3Q00616374696F6E7C696E7075740A7C746578747C2F626C63202825642B29031D3Q00616374696F6E7C696E7075740A7C746578747C2F424C43202825642B29030C3Q00202825642B252E3F25642A2903083Q00746F6E756D62657203083Q0064726F704974656D025Q008FC640030E3Q00426C61636B2047656D204C6F636B03013Q006202933Q002659012Q00920001000100043A012Q00920001002030000200010002001271010400036Q00020004000200062D000200200001000100043A012Q00200001002030000200010002001271010400046Q00020004000200062D000200200001000100043A012Q00200001002030000200010002001271010400056Q00020004000200062D000200200001000100043A012Q00200001002030000200010002001271010400066Q00020004000200062D000200200001000100043A012Q00200001002030000200010002001271010400076Q00020004000200062D000200200001000100043A012Q00200001002030000200010002001271010400086Q00020004000200068C0102009200013Q00043A012Q009200010012FA000200093Q00206700020002000A4Q000300013Q00122Q0004000B6Q00020004000200062Q000200480001000100043A012Q004800010012FA000200093Q00206700020002000A4Q000300013Q00122Q0004000C6Q00020004000200062Q000200480001000100043A012Q004800010012FA000200093Q00206700020002000A4Q000300013Q00122Q0004000D6Q00020004000200062Q000200480001000100043A012Q004800010012FA000200093Q00206700020002000A4Q000300013Q00122Q0004000E6Q00020004000200062Q000200480001000100043A012Q004800010012FA000200093Q00206700020002000A4Q000300013Q00122Q0004000F6Q00020004000200062Q000200480001000100043A012Q004800010012FA000200093Q0020CC00020002000A2Q0058000300013Q001271010400106Q0002000400020012FA000300093Q00208D00030003000A4Q000400013Q00122Q000500036Q000600023Q00122Q000700116Q0005000500074Q00030005000200062Q000300820001000100043A012Q008200010012FA000300093Q00208D00030003000A4Q000400013Q00122Q000500046Q000600023Q00122Q000700116Q0005000500074Q00030005000200062Q000300820001000100043A012Q008200010012FA000300093Q00208D00030003000A4Q000400013Q00122Q000500056Q000600023Q00122Q000700116Q0005000500074Q00030005000200062Q000300820001000100043A012Q008200010012FA000300093Q00208D00030003000A4Q000400013Q00122Q000500066Q000600023Q00122Q000700116Q0005000500074Q00030005000200062Q000300820001000100043A012Q008200010012FA000300093Q00208D00030003000A4Q000400013Q00122Q000500076Q000600023Q00122Q000700116Q0005000500074Q00030005000200062Q000300820001000100043A012Q008200010012FA000300093Q00208701030003000A4Q000400013Q00122Q000500086Q000600023Q00122Q000700116Q0005000500074Q00030005000200068C0103008B00013Q00043A012Q008B00010012FA000400124Q008D010500026Q00040002000200122Q000500126Q000600036Q0005000200024Q0002000400050012FA000400133Q001271010500144Q0058000600023Q001271010700153Q001271010800165Q00010400084Q003401046Q00573Q00017Q000A3Q00027Q004003043Q0066696E6403183Q00616374696F6E7C696E7075740A7C746578747C2F6472322003183Q00616374696F6E7C696E7075740A7C746578747C2F4452322003063Q00737472696E6703053Q006D61746368031D3Q00616374696F6E7C696E7075740A7C746578747C2F647232202825642B29031D3Q00616374696F6E7C696E7075740A7C746578747C2F445232202825642B29030C3Q00202825642B252E3F25642A2903093Q0052756E54687265616402333Q002659012Q00320001000100043A012Q00320001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102003200013Q00043A012Q003200010012FA000200053Q0020670002000200064Q000300013Q00122Q000400076Q00020004000200062Q000200180001000100043A012Q001800010012FA000200053Q0020CC0002000200062Q0058000300013Q001271010400086Q0002000400020012FA000300053Q00208D0003000300064Q000400013Q00122Q000500036Q000600023Q00122Q000700096Q0005000500074Q00030005000200062Q0003002A0001000100043A012Q002A00010012FA000300053Q0020870103000300064Q000400013Q00122Q000500046Q000600023Q00122Q000700096Q0005000500074Q0003000500020012FA0004000A3Q00068901053Q000100022Q00583Q00034Q00583Q00024Q00440104000200012Q0005010400014Q0099000400024Q005A00026Q00573Q00013Q00013Q00113Q0003083Q00746F6E756D62657203043Q006D61746803053Q00666C2Q6F72027Q0040026Q00084003073Q006F7665726D736703063Q00737472696E6703063Q00666F726D617403293Q00603243616C63756C6174696E6720603425642060323A206034322060327820603433203D2060322564030A3Q0053656E645061636B6574033E3Q00616374696F6E7C696E7075740A746578747C257320603243616C63756C6174696E6720603425642060323A206034322060327820603433203D206032256403073Q007465787465746303053Q00536C2Q6570025Q00408F4003043Q0044726F70030B3Q0070726F63652Q7344726F7003073Q0044726F2Q70656400344Q005900015Q00068C2Q01000B00013Q00043A012Q000B00010012FA000100014Q008B000200016Q00010002000200122Q000200016Q00038Q0002000200026Q0001000200044Q002C00010012FA000100023Q00204600010001000300122Q000200016Q000300016Q00020002000200202Q0002000200044Q00010002000200204Q0001000500122Q000100063Q00122Q000200073Q00202Q00020002000800122Q000300093Q00122Q000400016Q000500016Q0004000200024Q00058Q000200056Q00013Q000100122Q0001000A3Q00122Q000200043Q00122Q000300073Q00202Q00030003000800122Q0004000B3Q00122Q0005000C3Q00122Q000600016Q000700016Q0006000200024Q00078Q000300076Q00013Q000100122Q0001000D3Q00122Q0002000E6Q0001000200010012FA0001000F4Q00AE00028Q00010002000100122Q000100106Q00025Q00122Q000300116Q0001000300016Q00017Q000A3Q00027Q004003043Q0066696E6403193Q00616374696F6E7C696E7075740A7C746578747C2F647232782003193Q00616374696F6E7C696E7075740A7C746578747C2F445232582003063Q00737472696E6703053Q006D61746368031E3Q00616374696F6E7C696E7075740A7C746578747C2F64723278202825642B29031E3Q00616374696F6E7C696E7075740A7C746578747C2F44523258202825642B29030C3Q00202825642B252E3F25642A2903093Q0052756E54687265616402333Q002659012Q00320001000100043A012Q00320001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102003200013Q00043A012Q003200010012FA000200053Q0020670002000200064Q000300013Q00122Q000400076Q00020004000200062Q000200180001000100043A012Q001800010012FA000200053Q0020CC0002000200062Q0058000300013Q001271010400086Q0002000400020012FA000300053Q00208D0003000300064Q000400013Q00122Q000500036Q000600023Q00122Q000700096Q0005000500074Q00030005000200062Q0003002A0001000100043A012Q002A00010012FA000300053Q0020870103000300064Q000400013Q00122Q000500046Q000600023Q00122Q000700096Q0005000500074Q0003000500020012FA0004000A3Q00068901053Q000100022Q00583Q00034Q00583Q00024Q00440104000200012Q0005010400014Q0099000400024Q005A00026Q00573Q00013Q00013Q00113Q0003083Q00746F6E756D62657203043Q006D61746803053Q00666C2Q6F72027Q0040026Q00144003073Q006F7665726D736703063Q00737472696E6703063Q00666F726D617403293Q00603243616C63756C6174696E6720603425642060323A206034322060327820603435203D2060322564030A3Q0053656E645061636B6574033E3Q00616374696F6E7C696E7075740A746578747C257320603243616C63756C6174696E6720603425642060323A206034322060327820603435203D206032256403073Q007465787465746303053Q00536C2Q6570025Q00408F4003043Q0044726F70030B3Q0070726F63652Q7344726F7003073Q0044726F2Q70656400344Q005900015Q00068C2Q01000B00013Q00043A012Q000B00010012FA000100014Q008B000200016Q00010002000200122Q000200016Q00038Q0002000200026Q0001000200044Q002C00010012FA000100023Q00204600010001000300122Q000200016Q000300016Q00020002000200202Q0002000200044Q00010002000200204Q0001000500122Q000100063Q00122Q000200073Q00202Q00020002000800122Q000300093Q00122Q000400016Q000500016Q0004000200024Q00058Q000200056Q00013Q000100122Q0001000A3Q00122Q000200043Q00122Q000300073Q00202Q00030003000800122Q0004000B3Q00122Q0005000C3Q00122Q000600016Q000700016Q0006000200024Q00078Q000300076Q00013Q000100122Q0001000D3Q00122Q0002000E6Q0001000200010012FA0001000F4Q00AE00028Q00010002000100122Q000100106Q00025Q00122Q000300116Q0001000300016Q00017Q00013Q0003093Q0052756E54687265616404083Q0012FA000400013Q00068901053Q000100042Q00583Q00024Q00583Q00034Q00583Q00014Q00588Q00440104000200012Q00573Q00013Q00013Q00213Q0003083Q00746F6E756D62657203023Q006964025Q00406E40030C3Q004765744974656D436F756E74030D3Q0053656E645061636B657452617703043Q0074797065026Q00244003083Q00696E745F64617461025Q00109C4003053Q00536C2Q6570026Q0059402Q033Q006C6F6703063Q00737472696E6703063Q00666F726D6174031E3Q00603243616C63756C6174696E67206077256420602573257320603478256403053Q00636F6C6F7203043Q006E616D65030A3Q0053656E645061636B6574027Q004003313Q00616374696F6E7C696E7075740A746578747C25732043616C63756C6174696E67206077256420602573257320603478256403073Q0074657874657463026Q00894003153Q006032526573756C74203A206077256420602573257303283Q00616374696F6E7C696E7075740A746578747C257320526573756C74203A206077256420602573257303413Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C64726F700A6974656D5F64726F707C25647C0A6974656D5F636F756E747C256403293Q00616374696F6E7C696E7075740A746578747C257320603244726F2Q706564206077256420602573257303073Q006F7665726D736703143Q00603244726F2Q706564206077256420602573257303073Q004C6F6744726F7003493Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B6032257360775D20596F752776652044726F2Q70656420603525642060257325737C6C6566747C25647C0A03023Q006F7303043Q006461746503053Q0025483A254D00894Q00598Q0059000100013Q00068C2Q01000900013Q00043A012Q000900012Q005900015Q0012FA000200014Q0059000300014Q00C60002000200022Q00F83Q000100022Q0059000100024Q00F85Q00012Q0059000100033Q0020CC0001000100020026592Q01001C0001000300043A012Q001C00010012FA000100043Q001271010200034Q00C600010002000200064C0001001C00013Q00043A012Q001C00010012FA000100054Q00C000023Q000200302Q00020006000700302Q0002000800094Q00010002000100122Q0001000A3Q00122Q0002000B6Q0001000200010012FA0001000C3Q00126C0102000D3Q00202Q00020002000E00122Q0003000F6Q00048Q000500033Q00202Q0005000500104Q000600033Q00202Q0006000600114Q000700026Q000200074Q005D00013Q00010012FA000100123Q001271010200133Q0012FA0003000D3Q0020CC00030003000E001271010400143Q0012FA000500154Q005900066Q0059000700033Q0020CC0007000700102Q0059000800033Q0020CC0008000800112Q0059000900024Q00A1000300094Q005D00013Q00010012FA0001000A3Q001271010200164Q00442Q01000200010012FA0001000C3Q0012FA0002000D3Q0020CC00020002000E001271010300174Q005800046Q0059000500033Q0020CC0005000500102Q0059000600033Q0020CC0006000600112Q00A1000200064Q005D00013Q00010012FA000100123Q001271010200133Q0012FA0003000D3Q0020CC00030003000E001271010400183Q0012FA000500154Q005800066Q0059000700033Q0020CC0007000700102Q0059000800033Q0020CC0008000800112Q00A1000300084Q005D00013Q00010012FA0001000A3Q001271010200164Q00442Q01000200010012FA000100123Q001271010200133Q0012FA0003000D3Q0020CC00030003000E001271010400194Q0059000500033Q0020CC0005000500022Q005800066Q00A1000300064Q005D00013Q00010012FA000100123Q001271010200133Q0012FA0003000D3Q0020CC00030003000E0012710104001A3Q0012FA000500154Q005800066Q0059000700033Q0020CC0007000700102Q0059000800033Q0020CC0008000800112Q00A1000300084Q005D00013Q00010012FA0001001B3Q0012FA0002000D3Q0020CC00020002000E0012D90003001C6Q00048Q000500033Q00202Q0005000500104Q000600033Q00202Q0006000600114Q000200066Q00013Q000100122Q0001001D3Q00122Q0002000D3Q00202Q00020002000E00122Q0003001E3Q00122Q0004001F3Q00202Q00040004002000122Q000500216Q0004000200024Q00058Q000600033Q00202Q0006000600104Q000700033Q00202Q0007000700114Q000800033Q00202Q0008000800024Q0002000800024Q00010001000200122Q0001001D8Q00019Q002Q0002063Q00068901023Q000100032Q00588Q00583Q00014Q00598Q0099000200024Q00573Q00013Q00013Q00093Q00027Q004003063Q00737472696E6703063Q00666F726D617403203Q00616374696F6E7C696E7075740A7C746578747C2F257378256420282Q25642B2903073Q00636F2Q6D616E6403053Q006D6174636803053Q006C6F776572030C3Q00202825642B252E3F25642A2903083Q00746F6E756D62657202273Q002659012Q00240001000100043A012Q002400010012FA000200023Q0020CC000200020003001271010300044Q005900045Q0020CC0004000400052Q0059000500016Q0002000500020012FA000300023Q0020CC0003000300060020300004000100072Q00C60004000200022Q0058000500026Q00030005000200068C0103002400013Q00043A012Q002400012Q0058000400023Q001277000500086Q00040004000500122Q000500023Q00202Q00050005000600202Q0006000100074Q0006000200024Q000700046Q0005000700024Q000600026Q00076Q0059000800013Q001237000900096Q000A00036Q0009000200024Q000A00056Q0006000A00014Q000600016Q000600024Q000501026Q0099000200024Q00573Q00017Q00123Q00027Q004003043Q0066696E64031A3Q00616374696F6E7C696E7075740A7C746578747C2F73706C697420031A3Q00616374696F6E7C696E7075740A7C746578747C2F53504C49542003063Q00737472696E6703053Q006D61746368031F3Q00616374696F6E7C696E7075740A7C746578747C2F73706C6974202825642B29031F3Q00616374696F6E7C696E7075740A7C746578747C2F53504C4954202825642B29030C3Q004765744974656D436F756E74025Q00406E40025Q00109C40025Q0014BC40026Q005940025Q0088C34003083Q00746F6E756D62657203043Q0044726F70030B3Q0070726F63652Q7344726F7003073Q0044726F2Q70656402343Q002659012Q00330001000100043A012Q00330001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102003300013Q00043A012Q003300010012FA000200053Q0020670002000200064Q000300013Q00122Q000400076Q00020004000200062Q000200180001000100043A012Q001800010012FA000200053Q0020CC0002000200062Q0058000300013Q001271010400086Q0002000400020012FA000300093Q0012710104000A4Q00C60003000200020012FA000400093Q0012710105000B4Q00C60004000200020012FA000500093Q0012710106000C4Q00C600050002000200203C01060004000D2Q00F700060003000600203C01070005000E2Q00F70006000600070012FA0007000F4Q0058000800024Q00C60007000200022Q00F80006000600070020FB00060006000D0012FA000700104Q0097010800066Q00070002000100122Q000700116Q000800063Q00122Q000900126Q0007000900014Q000700016Q000700024Q00573Q00017Q000E3Q00027Q004003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F646177030C3Q004765744974656D436F756E74025Q00406E40025Q00109C40025Q0014BC40025Q008FC640026Q005940025Q0088C340024Q0080842E4103043Q0044726F70030B3Q0070726F63652Q7344726F7003073Q0044726F2Q70656402253Q002659012Q00220001000100043A012Q00220001002030000200010002001271010400036Q00020004000200068C0102002200013Q00043A012Q002200010012FA000200043Q001271010300054Q00C60002000200020012FA000300043Q001271010400064Q00C60003000200020012FA000400043Q001271010500074Q00C60004000200020012FA000500043Q001271010600084Q00C600050002000200203C0106000300092Q00F700060002000600203C01070004000A2Q00F700060006000700203C01070005000B2Q00F70006000600070012FA0007000C4Q0097010800066Q00070002000100122Q0007000D6Q000800063Q00122Q0009000E6Q0007000900014Q000700016Q000700024Q000501026Q0099000200024Q00573Q00017Q000B3Q00028Q0003103Q004F6E436F6E736F6C654D652Q73616765030E3Q006D652Q73616765636F6E736F6C65026Q00F03F03043Q006773756203173Q0043503A5F504C3A305F4F49443A5F43543A255B57255D5F034Q0003193Q0043503A305F504C3A345F4F49443A5F43543A255B5342255D5F03063Q002Q2A66726F6D03043Q006C6F673103193Q0060305B60636473632E2Q672F7761766570726F787960305D20021E3Q0020CC00023Q00010026590102001B0001000200043A012Q001B00010012FA000200033Q00068C0102001B00013Q00043A012Q001B00010020CC00023Q0004002030000200020005001271010400063Q001271010500076Q000200050002002030000200020005001271010400083Q001271010500076Q000200050002002030000200020005001271010400093Q001271010500076Q0002000500020012FA0003000A3Q0012710104000B4Q0058000500023Q001271010600074Q006F0104000400062Q00440103000200012Q0005010300014Q0099000300024Q000501026Q0099000200024Q00573Q00017Q00693Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF03023Q006F7303043Q006461746503053Q0025483A254D026Q00F03F03153Q000A7365745F64656661756C745F636F6C6F727C606F033A3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C606340576176652050726F787920436F6E6669674Q607C6C6566747C33327C03463Q000A612Q645F696D6167655F62752Q746F6E7C62612Q6E65727C63616368652F696E746572666163652F6C617267652F62612Q6E65722E722Q7465787C6E6F666C6167733Q7C03123Q000A612Q645F7370616365727C736D612Q6C7C03253Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6030603248652Q6C6F60302003083Q004765744C6F63616C03043Q006E616D65030B3Q007C6C6566747C363237387C03273Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C60306032576F726C646030203A2003083Q00476574576F726C64030B3Q00207C6C6566747C3237387C032B3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C60306032446174652054696D656030203A20033E3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6039576176652050726F787920436F6E66696775726174696F6E7C6C6566747C37312Q387C033E3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C606342544B20436F6E66696775726174696F6E204C6973747C6C6566747C3334307C031C3Q000A612Q645F637573746F6D5F6D617267696E7C783A303B793A31307C033C3Q000A612Q645F636865636B626F787C416374697661746567656D73636865636B65727C6032416374697661746520603947656D7320436865636B65727C03133Q00416374697661746567656D73636865636B657203013Q007C031D3Q000A612Q645F637573746F6D5F6D617267696E7C783A303B793A2D33327C03563Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C2053686F7720486F77204D7563682047656D732044726F2Q7065647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03353Q000A612Q645F636865636B626F787C57692Q6E6572317C60322041637469766174652060394175746F2044726F702057692Q6E65727C03073Q0057692Q6E65723103693Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F6D61746963612Q6C792044726F7020546F2057692Q6E6572205768656E202F636120697320557365647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03323Q000A612Q645F636865636B626F787C4368616E64317C60322041637469766174652060394175746F20507574204368616E647C03063Q004368616E643103643Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F6D61746963612Q6C7920507574204368616E64205768656E202F636120697320557365647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03593Q000A612Q645F636865636B626F787C6163746976617370616D6C777C60324163746976617465206039416C77617973205475726E204F6E205370616D205768656E202F7470206F72202F636120697320446F6E6520557365647C030C3Q006163746976617370616D6C77033B3Q000A612Q645F636865636B626F787C73686F77652Q666563747C603220416374697661746520603953686F7720652Q6665637473206F6E2042544B7C030A3Q0073686F77652Q6665637403563Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C2053686F7720452Q6665637473204F6E202F7470206F72202F63617C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03323Q000A612Q645F636865636B626F787C416374697661746562746B6C6F677C6032416374697661746520603942544B206C6F677C030E3Q00416374697661746562746B6C6F67035D3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C2053686F7720576562682Q6F6B204C6F67205768656E202F747020697320557365647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03413Q000A612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C6063436173696E6F20436F6E66696775726174696F6E204C6973747C6C6566747C3735387C03393Q000A612Q645F636865636B626F787C416374697661746566616B656C6F677C6032416374697661746520603946616B65205370696E204C6F677C030F3Q00416374697661746566616B656C6F6703663Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C2053686F772046616B65205370696E204C6F67205768656E2046616B6520547970652044657465637465647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03393Q000A612Q645F636865636B626F787C41637469766174657061746866696E6465727C603241637469766174652060395061746846696E6465727C03123Q0041637469766174657061746866696E646572034F3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204163746976617465205061746846696E6465727C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C034E3Q000A612Q645F636865636B626F787C4163746976617761726E696E676F6E6A6F696E7C603241637469766174652060345761726E696E67204D652Q73616765204F6E204A6F696E20576F726C64207C03133Q004163746976617761726E696E676F6E6A6F696E03583Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C2053686F77205761726E696E67204D652Q73616765204F6E204A6F696E7C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03473Q000A612Q645F636865636B626F787C4163746976617761726E696E676F6E6A6F696E327C603241637469766174652060634D652Q73616765204F6E204A6F696E20576F726C64207C03143Q004163746976617761726E696E676F6E6A6F696E3203503Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C2053686F77204D652Q73616765204F6E204A6F696E7C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C033B3Q000A612Q645F636865636B626F787C416374697661636F6E766572747C603241637469766174652060394175746F20436F6E76657274204C6F636B7C030D3Q00416374697661636F6E7665727403743Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F6D61746963612Q6C7920436F6D7072652Q7320312Q3020576C7320496E746F203120446C205768656E20436F2Q6C65637465642E7C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C033A3Q000A612Q645F636865636B626F787C416374697661666173747C603241637469766174652060394175746F20466173742054656C6570686F6E657C030A3Q0041637469766166617374037E3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F6D61746963612Q6C7920436F6E7665727420596F757220312Q30446C7320546F2042474C205768656E205772656E6368696E67205468652050686F6E652E7C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C033E3Q000A612Q645F636865636B626F787C416374697661636F6C656B7C6032416374697661746520603953686F7720436F2Q6C6563746564204D652Q736167657C030B3Q00416374697661636F6C656B03623Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C2053686F7720436F2Q6C6563746564204D652Q73616765205768656E20436F2Q6C65637465642E7C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03453Q000A612Q645F636865636B626F787C4163746976616E616D657C603241637469766174652060394368616E67652050726F7879205465787420546F20596F7572204E616D657C030A3Q004163746976616E616D65035C3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204368616E67696E672050726F7879205465787420546F20596F7572204E616D657C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03393Q000A612Q645F636865636B626F787C4163746976617370692Q6E616D657C603241637469766174652060394C617374205370696E204E616D657C030E3Q004163746976617370692Q6E616D65035A3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C2053686F77204C617374205370696E204E616D65204F6E205370692Q6E65647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03503Q000A612Q645F636865636B626F787C616374697661636F6E736F6C657C60324163746976617465206039416C77617973204D616B652054686520436F6E736F6C6520486176652057617465726D61726B7C030D3Q00616374697661636F6E736F6C6503A73Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C20416C77617973204D616B652054686520436F6E736F6C6520486176652057617465726D61726B20212060344E6F7465203A20486176652054686973204163746976617465204D6179204D616B6520576F726C6420416E642053797374656D205461622057692Q6C204275677C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03513Q000A612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60634175746F2042616E20436F6E66696775726174696F6E20436F6E73756D61626C6573204C6973747C6C6566747C31343834367C033F3Q000A612Q645F636865636B626F787C41637469766174656175746F62616E317C603241637469766174652060394175746F2042616E2048656E6368204D616E7C03103Q0041637469766174656175746F62616E31035A3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F2042616E2049662048656E6368204D616E2044657465637465647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03403Q000A612Q645F636865636B626F787C41637469766174656175746F62616E327C603241637469766174652060394175746F2042616E204372696D6520576176657C03103Q0041637469766174656175746F62616E32035B3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F2042616E204966204372696D6520576176652044657465637465647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03453Q000A612Q645F636865636B626F787C41637469766174656175746F62616E337C603241637469766174652060394175746F2042616E2050797363686F7469632042752Q6E797C03103Q0041637469766174656175746F62616E3303603Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F2042616E2049662050797363686F7469632042752Q6E792044657465637465647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03493Q000A612Q645F636865636B626F787C41637469766174656175746F62616E347C603241637469766174652060394175746F2042616E2050657420547261696E65722057686973746C657C03103Q0041637469766174656175746F62616E3403643Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F2042616E2049662050657420547261696E65722057686973746C652044657465637465647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03443Q000A612Q645F636865636B626F787C41637469766174656175746F62616E357C603241637469766174652060394175746F2042616E20446173205265642042616C2Q6F6E7C03103Q0041637469766174656175746F62616E35035F3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F2042616E20496620446173205265642042616C2Q6F6E2044657465637465647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C033E3Q000A612Q645F636865636B626F787C41637469766174656175746F62616E367C603241637469766174652060394175746F2042616E20536E6F7762612Q6C7C03103Q0041637469766174656175746F62616E3603593Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F2042616E20496620536E6F7762612Q6C2044657465637465647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03493Q000A612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C6063416374697661746520546865204175746F2042616E20436F6E73756D61626C65737C6C6566747C3137367C034B3Q000A612Q645F636865636B626F787C41637469766174656175746F62616E66696E616C657C603241637469766174652060394175746F2042616E20436F6E73756D61626C6573204C6973747C03153Q0041637469766174656175746F62616E66696E616C6503653Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204175746F2042616E2049662054686520436F6E73756D61626C6573204C6973742044657465637465647C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C033E3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60635361766520416E64204C6F616420436F6E6669677C6C6566747C31303633387C03283Q000A746578745F7363616C696E675F737472696E677C696D6C2Q6F6B696E672Q73636F3Q316F6C7C03263Q000A612Q645F62752Q746F6E7C62746B636F6E6669677C6032412Q706C79204368616E6765737C032F3Q000A612Q645F62752Q746F6E7C636F6E666967736176657C60325361766520603450726F7879206063436F6E6669677C032F3Q000A612Q645F62752Q746F6E7C636F6E6669676C6F61647C60324C6F616420603450726F7879206063436F6E6669677C03343Q000A612Q645F62752Q746F6E7C736176657C60325361766520603442544B206030416E642060345350414D206063436F6E6669677C03343Q000A612Q645F62752Q746F6E7C6C6F61647C60324C6F616420603442544B206030416E642060345350414D206063436F6E6669677C031B3Q000A656E645F6469616C6F677C636C6F73652Q7C6034436C6F73657C030B3Q0053656E645661726C69737400BC4Q0053016Q00304Q0001000200304Q0003000400122Q000100053Q00202Q00010001000600122Q000200076Q00010002000200122Q000200093Q00122Q0003000A3Q00122Q0004000B3Q0012710105000C3Q0012D00006000D3Q00122Q0007000E6Q00070001000200202Q00070007000F00122Q000800103Q00122Q000900113Q00122Q000A00126Q000A0001000200202Q000A000A000F00122Q000B00133Q001271010C00144Q0058000D00013Q001271010E00133Q001271010F000C3Q00121A011000153Q00122Q0011000C3Q00122Q001200163Q00122Q001300173Q00122Q001400183Q00122Q001500193Q00122Q0016001A3Q00122Q0017001B3Q00122Q0018001C3Q00122Q001900173Q001271011A001D3Q001214001B001E3Q00122Q001C001A3Q00122Q001D001B3Q00122Q001E001F3Q00122Q001F00173Q00122Q002000203Q00122Q002100213Q00122Q0022001A3Q00122Q0023001B3Q00122Q002400223Q001275002500173Q00122Q002600233Q00122Q002700243Q00122Q0028001A3Q00122Q0029001B3Q00122Q002A00223Q00122Q002B00173Q00122Q002C00253Q00122Q002D00263Q00122Q002E001A3Q0012CD002F001B3Q00122Q003000273Q00122Q003100173Q00122Q003200283Q00122Q003300293Q00122Q0034001A3Q00122Q0035001B3Q00122Q0036002A3Q00122Q0037000C3Q00122Q0038002B3Q001275003900173Q00122Q003A002C3Q00122Q003B002D3Q00122Q003C001A3Q00122Q003D001B3Q00122Q003E002E3Q00122Q003F00173Q00122Q0040002F3Q00122Q004100303Q00122Q0042001A3Q0012CD0043001B3Q00122Q004400313Q00122Q004500173Q00122Q004600323Q00122Q004700333Q00122Q0048001A3Q00122Q0049001B3Q00122Q004A00343Q00122Q004B00173Q00122Q004C00353Q001214004D00363Q00122Q004E001A3Q00122Q004F001B3Q00122Q005000373Q00122Q005100173Q00122Q005200383Q00122Q005300393Q00122Q0054001A3Q00122Q0055001B3Q00122Q0056003A3Q001275005700173Q00122Q0058003B3Q00122Q0059003C3Q00122Q005A001A3Q00122Q005B001B3Q00122Q005C003D3Q00122Q005D00173Q00122Q005E003E3Q00122Q005F003F3Q00122Q0060001A3Q0012CD0061001B3Q00122Q006200403Q00122Q006300173Q00122Q006400413Q00122Q006500423Q00122Q0066001A3Q00122Q0067001B3Q00122Q006800433Q00122Q006900173Q00122Q006A00443Q001214006B00453Q00122Q006C001A3Q00122Q006D001B3Q00122Q006E00463Q00122Q006F00173Q00122Q007000473Q00122Q007100483Q00122Q0072001A3Q00122Q0073001B3Q00122Q007400493Q0012CD0075000C3Q00122Q0076004A3Q00122Q007700173Q00122Q0078004B3Q00122Q0079004C3Q00122Q007A001A3Q00122Q007B001B3Q00122Q007C004D3Q00122Q007D00173Q00122Q007E004E3Q001214007F004F3Q00122Q0080001A3Q00122Q0081001B3Q00122Q008200503Q00122Q008300173Q00122Q008400513Q00122Q008500523Q00122Q0086001A3Q00122Q0087001B3Q00122Q008800533Q001275008900173Q00122Q008A00543Q00122Q008B00553Q00122Q008C001A3Q00122Q008D001B3Q00122Q008E00563Q00122Q008F00173Q00122Q009000573Q00122Q009100583Q00122Q0092001A3Q0012CD0093001B3Q00122Q009400593Q00122Q009500173Q00122Q0096005A3Q00122Q0097005B3Q00122Q0098001A3Q00122Q0099001B3Q00122Q009A005C3Q00122Q009B000C3Q00122Q009C005D3Q001271019D00173Q001271019E005E3Q0012FA009F005F3Q00126400A0001A3Q00122Q00A1001B3Q00122Q00A200603Q00122Q00A3000C3Q00122Q00A400613Q00122Q00A5000C3Q00122Q00A600623Q00122Q00A700633Q00122Q00A800643Q00122Q00A900653Q00127101AA00663Q00127101AB00673Q00127101AC00684Q00800102000200AC00104Q0008000200122Q000200696Q00038Q0002000200016Q00017Q008A3Q0003043Q0067737562032A3Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C62746B636F6E666967034Q0003013Q000A03073Q0057692Q6E65723103083Q00746F6E756D62657203053Q006D61746368030D3Q0057692Q6E6572317C2825642B2903063Q004368616E6431030C3Q004368616E64317C2825642B29030A3Q0073686F77652Q6665637403103Q0073686F77652Q666563747C2825642B29030E3Q00416374697661746562746B6C6F6703143Q00416374697661746562746B6C6F677C2825642B29030F3Q00416374697661746566616B656C6F6703153Q00416374697661746566616B656C6F677C2825642B2903123Q0041637469766174657061746866696E64657203183Q0041637469766174657061746866696E6465727C2825642B2903133Q004163746976617761726E696E676F6E6A6F696E03193Q004163746976617761726E696E676F6E6A6F696E7C2825642B29030D3Q00416374697661636F6E7665727403133Q00416374697661636F6E766572747C2825642B29030A3Q004163746976616661737403103Q00416374697661666173747C2825642B29030B3Q00416374697661636F6C656B03113Q00416374697661636F6C656B7C2825642B29030A3Q004163746976616E616D6503103Q004163746976616E616D657C2825642B29030E3Q004163746976617370692Q6E616D6503143Q004163746976617370692Q6E616D657C2825642B2903133Q00416374697661746567656D73636865636B657203193Q00416374697661746567656D73636865636B65727C2825642B29030C3Q006163746976617370616D6C7703123Q006163746976617370616D6C777C2825642B29030D3Q00616374697661636F6E736F6C6503133Q00616374697661636F6E736F6C657C2825642B2903103Q0041637469766174656175746F62616E3103163Q0041637469766174656175746F62616E317C2825642B2903103Q0041637469766174656175746F62616E3203163Q0041637469766174656175746F62616E327C2825642B2903103Q0041637469766174656175746F62616E3303163Q0041637469766174656175746F62616E337C2825642B2903103Q0041637469766174656175746F62616E3403163Q0041637469766174656175746F62616E347C2825642B2903103Q0041637469766174656175746F62616E3503163Q0041637469766174656175746F62616E357C2825642B2903103Q0041637469766174656175746F62616E3603163Q0041637469766174656175746F62616E367C2825642B2903153Q0041637469766174656175746F62616E66696E616C65031B3Q0041637469766174656175746F62616E66696E616C657C2825642B2903143Q004163746976617761726E696E676F6E6A6F696E32031A3Q004163746976617761726E696E676F6E6A6F696E327C2825642B29026Q00F03F03083Q007761726E696E67322Q033Q006C6F6703203Q0060394D652Q73616765206F6E204A6F696E2073657420746F3A60322074727565028Q0003213Q0060394D652Q73616765206F6E204A6F696E2073657420746F3A60342066616C736503023Q00617703213Q0060394175746F2044726F702057692Q6E65722073657420746F3A6032207472756503223Q0060394175746F2044726F702057692Q6E65722073657420746F3A60342066616C736503023Q007063031F3Q0060394175746F20507574204368616E642073657420746F3A6032207472756503203Q0060394175746F20507574204368616E642073657420746F3A60342066616C736503063Q00652Q6665637403243Q00603953686F7720652Q6665637473206F6E2042544B2073657420746F3A6032207472756503253Q00603953686F7720652Q6665637473206F6E2042544B2073657420746F3A60342066616C736503073Q00776562682Q6F6B03213Q00603941637469766174652042544B206C6F672073657420746F3A6032207472756503223Q00603941637469766174652042544B206C6F672073657420746F3A60342066616C736503073Q0066616B656C6F6703273Q00603941637469766174652046616B65205370696E206C6F672073657420746F3A6032207472756503283Q00603941637469766174652046616B65205370696E206C6F672073657420746F3A60342066616C7365030A3Q0045646974546F2Q676C65030A3Q005061746846696E64657203243Q0060394163746976617465205061746846696E6465722073657420746F3A6032207472756503253Q0060394163746976617465205061746846696E6465722073657420746F3A60342066616C736503073Q007761726E696E6703313Q0060394163746976617465205761726E696E67204D652Q73616765204F6E204A6F696E2073657420746F3A6032207472756503323Q0060394163746976617465205761726E696E67204D652Q73616765204F6E204A6F696E2073657420746F3A60342066616C736503053Q006175746F63032B3Q0060394163746976617465204175746F20436F6E76657274204C6F636B2073657420746F3A60322074727565032C3Q0060394163746976617465204175746F20436F6E76657274204C6F636B2073657420746F3A60342066616C736503043Q006661737403233Q00603941637469766174652046617374204D6F64652073657420746F3A6032207472756503243Q00603941637469766174652046617374204D6F64652073657420746F3A60342066616C736503143Q0073686F77436F2Q6C6563746564456E61626C656403243Q006039416374697661746520436F6C656B204D6F64652073657420746F3A6032207472756503253Q006039416374697661746520436F6C656B204D6F64652073657420746F3A60342066616C736503073Q007465787465746303083Q004765744C6F63616C03043Q006E616D6503043Q00282E2A2903063Q0060652531606F03233Q0060394163746976617465204E616D65204D6F64652073657420746F3A6032207472756503143Q0060775B606320576176652050726F78792060775D03243Q0060394163746976617465204E616D65204D6F64652073657420746F3A60342066616C736503073Q007370696E616D6503083Q007370696E616D6532030F3Q004163746976617370692Q6E616D6532032D3Q0060394163746976617465204C617374205370696E204E616D65204D6F64652073657420746F3A60322074727565032E3Q0060394163746976617465204C617374205370696E204E616D65204D6F64652073657420746F3A60342066616C7365030B3Q0047656D73436865636B657203263Q00603941637469766174652047656D7320436865636B65722073657420746F3A6032207472756503273Q00603941637469766174652047656D7320436865636B65722073657420746F3A60342066616C736503063Q007370616D6C7703233Q0060394163746976617465205370616D204D6F64652073657420746F3A6032207472756503243Q0060394163746976617465205370616D204D6F64652073657420746F3A60342066616C7365030E3Q006D652Q73616765636F6E736F6C6503283Q006039416374697661746520436F6E736F6C652057617465726D61726B20746F3A60342066616C736503273Q006039416374697661746520436F6E736F6C652057617465726D61726B20746F3A6032207472756503083Q0048656E63686D616E032B3Q0060394163746976617465204175746F2042616E2048656E63686D616E2073657420746F3A60322074727565032C3Q0060394163746976617465204175746F2042616E2048656E63686D616E2073657420746F3A60342066616C736503093Q004372696D6557617665032C3Q0060394163746976617465204175746F2042616E204372696D65576176652073657420746F3A60322074727565032D3Q0060394163746976617465204175746F2042616E204372696D65576176652073657420746F3A60342066616C7365030E3Q0050737963686F74696342752Q6E7903313Q0060394163746976617465204175746F2042616E2050737963686F74696342752Q6E792073657420746F3A6032207472756503323Q0060394163746976617465204175746F2042616E2050737963686F74696342752Q6E792073657420746F3A60342066616C736503113Q00506574547261696E657257686973746C6503343Q0060394163746976617465204175746F2042616E20506574547261696E657257686973746C652073657420746F3A6032207472756503353Q0060394163746976617465204175746F2042616E20506574547261696E657257686973746C652073657420746F3A60342066616C7365030D3Q0044617352656442612Q6C2Q6F6E03303Q0060394163746976617465204175746F2042616E2044617352656442612Q6C2Q6F6E2073657420746F3A6032207472756503313Q0060394163746976617465204175746F2042616E2044617352656442612Q6C2Q6F6E2073657420746F3A60342066616C736503083Q00536E6F7742612Q6C032B3Q0060394163746976617465204175746F2042616E20536E6F7742612Q6C2073657420746F3A60322074727565032C3Q0060394163746976617465204175746F2042616E20536E6F7742612Q6C2073657420746F3A60342066616C736503123Q004175746F42616E436F6E73756D61626C6573032E3Q0060394163746976617465204175746F2042616E20436F6E73756D61626C65732073657420746F3A60322074727565032F3Q0060394163746976617465204175746F2042616E20436F6E73756D61626C65732073657420746F3A60342066616C736503073Q006F7665726D736703193Q00606320436F6E66696775726174696F6E20612Q706C69656420030A3Q0053656E645061636B6574027Q004003123Q00616374696F6E7C696E7075740A746578747C03183Q00206065436F6E66696775726174696F6E20412Q706C6965640180022Q00209700013Q000100122Q000300023Q00122Q000400036Q00010004000200202Q00010001000100122Q000300043Q00122Q000400036Q00010004000200122Q000200063Q00202Q000300010007001271010500086Q00030005000200062D0003000F0001000100043A012Q000F00010012FA000300054Q00C60002000200020012FF000200053Q00122Q000200063Q00202Q00030001000700122Q0005000A6Q00030005000200062Q000300180001000100043A012Q001800010012FA000300094Q00C60002000200020012FF000200093Q00122Q000200063Q00202Q00030001000700122Q0005000C6Q00030005000200062Q000300210001000100043A012Q002100010012FA0003000B4Q00C60002000200020012FF0002000B3Q00122Q000200063Q00202Q00030001000700122Q0005000E6Q00030005000200062Q0003002A0001000100043A012Q002A00010012FA0003000D4Q00C60002000200020012FF0002000D3Q00122Q000200063Q00202Q00030001000700122Q000500106Q00030005000200062Q000300330001000100043A012Q003300010012FA0003000F4Q00C60002000200020012FF0002000F3Q00122Q000200063Q00202Q00030001000700122Q000500126Q00030005000200062Q0003003C0001000100043A012Q003C00010012FA000300114Q00C60002000200020012FF000200113Q00122Q000200063Q00202Q00030001000700122Q000500146Q00030005000200062Q000300450001000100043A012Q004500010012FA000300134Q00C60002000200020012FF000200133Q00122Q000200063Q00202Q00030001000700122Q000500166Q00030005000200062Q0003004E0001000100043A012Q004E00010012FA000300154Q00C60002000200020012FF000200153Q00122Q000200063Q00202Q00030001000700122Q000500186Q00030005000200062Q000300570001000100043A012Q005700010012FA000300174Q00C60002000200020012FF000200173Q00122Q000200063Q00202Q00030001000700122Q0005001A6Q00030005000200062Q000300600001000100043A012Q006000010012FA000300194Q00C60002000200020012FF000200193Q00122Q000200063Q00202Q00030001000700122Q0005001C6Q00030005000200062Q000300690001000100043A012Q006900010012FA0003001B4Q00C60002000200020012FF0002001B3Q00122Q000200063Q00202Q00030001000700122Q0005001E6Q00030005000200062Q000300720001000100043A012Q007200010012FA0003001D4Q00C60002000200020012FF0002001D3Q00122Q000200063Q00202Q00030001000700122Q000500206Q00030005000200062Q0003007B0001000100043A012Q007B00010012FA0003001F4Q00C60002000200020012FF0002001F3Q00122Q000200063Q00202Q00030001000700122Q000500226Q00030005000200062Q000300840001000100043A012Q008400010012FA000300214Q00C60002000200020012FF000200213Q00122Q000200063Q00202Q00030001000700122Q000500246Q00030005000200062Q0003008D0001000100043A012Q008D00010012FA000300234Q00C60002000200020012FF000200233Q00122Q000200063Q00202Q00030001000700122Q000500266Q00030005000200062Q000300960001000100043A012Q009600010012FA000300254Q00C60002000200020012FF000200253Q00122Q000200063Q00202Q00030001000700122Q000500286Q00030005000200062Q0003009F0001000100043A012Q009F00010012FA000300274Q00C60002000200020012FF000200273Q00122Q000200063Q00202Q00030001000700122Q0005002A6Q00030005000200062Q000300A80001000100043A012Q00A800010012FA000300294Q00C60002000200020012FF000200293Q00122Q000200063Q00202Q00030001000700122Q0005002C6Q00030005000200062Q000300B10001000100043A012Q00B100010012FA0003002B4Q00C60002000200020012FF0002002B3Q00122Q000200063Q00202Q00030001000700122Q0005002E6Q00030005000200062Q000300BA0001000100043A012Q00BA00010012FA0003002D4Q00C60002000200020012FF0002002D3Q00122Q000200063Q00202Q00030001000700122Q000500306Q00030005000200062Q000300C30001000100043A012Q00C300010012FA0003002F4Q00C60002000200020012FF0002002F3Q00122Q000200063Q00202Q00030001000700122Q000500326Q00030005000200062Q000300CC0001000100043A012Q00CC00010012FA000300314Q00C60002000200020012FF000200313Q00122Q000200063Q00202Q00030001000700122Q000500346Q00030005000200062Q000300D50001000100043A012Q00D500010012FA000300334Q00C600020002000200120A000200333Q0012FA000200333Q002659010200DF0001003500043A012Q00DF00012Q0005010200013Q00120A000200363Q0012FA000200373Q001271010300384Q00440102000200010012FA000200333Q002659010200E70001003900043A012Q00E700012Q000501025Q00120A000200363Q0012FA000200373Q0012710103003A4Q00440102000200010012FA000200053Q002659010200EF0001003500043A012Q00EF00012Q0005010200013Q00120A0002003B3Q0012FA000200373Q0012710103003C4Q00440102000200010012FA000200053Q002659010200F70001003900043A012Q00F700012Q000501025Q00120A0002003B3Q0012FA000200373Q0012710103003D4Q00440102000200010012FA000200093Q002659010200FF0001003500043A012Q00FF00012Q0005010200013Q00120A0002003E3Q0012FA000200373Q0012710103003F4Q00440102000200010012FA000200093Q002659010200072Q01003900043A012Q00072Q012Q000501025Q00120A0002003E3Q0012FA000200373Q001271010300404Q00440102000200010012FA0002000B3Q0026590102000F2Q01003500043A012Q000F2Q012Q0005010200013Q00120A000200413Q0012FA000200373Q001271010300424Q00440102000200010012FA0002000B3Q002659010200172Q01003900043A012Q00172Q012Q000501025Q00120A000200413Q0012FA000200373Q001271010300434Q00440102000200010012FA0002000D3Q0026590102001F2Q01003500043A012Q001F2Q012Q0005010200013Q00120A000200443Q0012FA000200373Q001271010300454Q00440102000200010012FA0002000D3Q002659010200272Q01003900043A012Q00272Q012Q000501025Q00120A000200443Q0012FA000200373Q001271010300464Q00440102000200010012FA0002000F3Q0026590102002F2Q01003500043A012Q002F2Q012Q0005010200013Q00120A000200473Q0012FA000200373Q001271010300484Q00440102000200010012FA0002000F3Q002659010200372Q01003900043A012Q00372Q012Q000501025Q00120A000200473Q0012FA000200373Q001271010300494Q00440102000200010012FA000200113Q002659010200412Q01003500043A012Q00412Q010012FA0002004A3Q0012160103004B6Q000400016Q00020004000100122Q000200373Q00122Q0003004C6Q0002000200010012FA000200113Q0026590102004B2Q01003900043A012Q004B2Q010012FA0002004A3Q0012160103004B6Q00048Q00020004000100122Q000200373Q00122Q0003004D6Q0002000200010012FA000200133Q002659010200532Q01003500043A012Q00532Q012Q0005010200013Q00120A0002004E3Q0012FA000200373Q0012710103004F4Q00440102000200010012FA000200133Q0026590102005B2Q01003900043A012Q005B2Q012Q000501025Q00120A0002004E3Q0012FA000200373Q001271010300504Q00440102000200010012FA000200153Q002659010200632Q01003500043A012Q00632Q012Q0005010200013Q00120A000200513Q0012FA000200373Q001271010300524Q00440102000200010012FA000200153Q0026590102006B2Q01003900043A012Q006B2Q012Q000501025Q00120A000200513Q0012FA000200373Q001271010300534Q00440102000200010012FA000200173Q002659010200732Q01003500043A012Q00732Q012Q0005010200013Q00120A000200543Q0012FA000200373Q001271010300554Q00440102000200010012FA000200173Q0026590102007B2Q01003900043A012Q007B2Q012Q000501025Q00120A000200543Q0012FA000200373Q001271010300564Q00440102000200010012FA000200193Q002659010200832Q01003500043A012Q00832Q012Q0005010200013Q00120A000200573Q0012FA000200373Q001271010300584Q00440102000200010012FA000200193Q0026590102008B2Q01003900043A012Q008B2Q012Q000501025Q00120A000200573Q0012FA000200373Q001271010300594Q00440102000200010012FA0002001B3Q002659010200992Q01003500043A012Q00992Q010012FA0002005B4Q00960102000100020020CC00020002005C0020300002000200010012710104005D3Q0012710105005E6Q00020005000200120A0002005A3Q0012FA000200373Q0012710103005F4Q00440102000200010012FA0002001B3Q002659010200A12Q01003900043A012Q00A12Q01001271010200603Q00120A0002005A3Q0012FA000200373Q001271010300614Q00440102000200010012FA0002001D3Q002659010200AD2Q01003500043A012Q00AD2Q012Q0005010200013Q001253000200626Q00025Q00122Q000200633Q00122Q000200393Q00122Q000200643Q00122Q000200373Q00122Q000300656Q0002000200010012FA0002001D3Q002659010200B52Q01003900043A012Q00B52Q012Q000501025Q00120A000200623Q0012FA000200373Q001271010300664Q00440102000200010012FA0002001F3Q002659010200BF2Q01003500043A012Q00BF2Q010012FA0002004A3Q001216010300676Q000400016Q00020004000100122Q000200373Q00122Q000300686Q0002000200010012FA0002001F3Q002659010200C92Q01003900043A012Q00C92Q010012FA0002004A3Q001216010300676Q00048Q00020004000100122Q000200373Q00122Q000300696Q0002000200010012FA000200213Q002659010200D12Q01003500043A012Q00D12Q012Q0005010200013Q00120A0002006A3Q0012FA000200373Q0012710103006B4Q00440102000200010012FA000200213Q002659010200D92Q01003900043A012Q00D92Q012Q000501025Q00120A0002006A3Q0012FA000200373Q0012710103006C4Q00440102000200010012FA000200233Q002659010200E12Q01003900043A012Q00E12Q012Q000501025Q00120A0002006D3Q0012FA000200373Q0012710103006E4Q00440102000200010012FA000200233Q002659010200E92Q01003500043A012Q00E92Q012Q0005010200013Q00120A0002006D3Q0012FA000200373Q0012710103006F4Q00440102000200010012FA000200253Q002659010200F32Q01003500043A012Q00F32Q010012FA0002004A3Q001216010300706Q000400016Q00020004000100122Q000200373Q00122Q000300716Q0002000200010012FA000200253Q002659010200FD2Q01003900043A012Q00FD2Q010012FA0002004A3Q001216010300706Q00048Q00020004000100122Q000200373Q00122Q000300726Q0002000200010012FA000200273Q002659010200070201003500043A012Q000702010012FA0002004A3Q001216010300736Q000400016Q00020004000100122Q000200373Q00122Q000300746Q0002000200010012FA000200273Q002659010200110201003900043A012Q001102010012FA0002004A3Q001216010300736Q00048Q00020004000100122Q000200373Q00122Q000300756Q0002000200010012FA000200293Q0026590102001B0201003500043A012Q001B02010012FA0002004A3Q001216010300766Q000400016Q00020004000100122Q000200373Q00122Q000300776Q0002000200010012FA000200293Q002659010200250201003900043A012Q002502010012FA0002004A3Q001216010300766Q00048Q00020004000100122Q000200373Q00122Q000300786Q0002000200010012FA0002002B3Q0026590102002F0201003500043A012Q002F02010012FA0002004A3Q001216010300796Q000400016Q00020004000100122Q000200373Q00122Q0003007A6Q0002000200010012FA0002002B3Q002659010200390201003900043A012Q003902010012FA0002004A3Q001216010300796Q00048Q00020004000100122Q000200373Q00122Q0003007B6Q0002000200010012FA0002002D3Q002659010200430201003500043A012Q004302010012FA0002004A3Q0012160103007C6Q000400016Q00020004000100122Q000200373Q00122Q0003007D6Q0002000200010012FA0002002D3Q0026590102004D0201003900043A012Q004D02010012FA0002004A3Q0012160103007C6Q00048Q00020004000100122Q000200373Q00122Q0003007E6Q0002000200010012FA0002002F3Q002659010200570201003500043A012Q005702010012FA0002004A3Q0012160103007F6Q000400016Q00020004000100122Q000200373Q00122Q000300806Q0002000200010012FA0002002F3Q002659010200610201003900043A012Q006102010012FA0002004A3Q0012160103007F6Q00048Q00020004000100122Q000200373Q00122Q000300816Q0002000200010012FA000200313Q0026590102006B0201003500043A012Q006B02010012FA0002004A3Q001216010300826Q000400016Q00020004000100122Q000200373Q00122Q000300836Q0002000200010012FA000200313Q002659010200750201003900043A012Q007502010012FA0002004A3Q001216010300826Q00048Q00020004000100122Q000200373Q00122Q000300846Q0002000200010012FA000200853Q001271010300864Q00440102000200010012FA000200873Q0012B5000300883Q00122Q000400893Q00122Q0005005A3Q00122Q0006008A6Q0004000400064Q0002000400012Q00573Q00017Q000C3Q00027Q004003043Q0066696E64031A3Q00616374696F6E7C696E7075740A7C746578747C2F636F6E666967031A3Q00616374696F6E7C696E7075740A7C746578747C2F434F4E464947031A3Q00616374696F6E7C696E7075740A7C746578747C2F6F7074696F6E031A3Q00616374696F6E7C696E7075740A7C746578747C2F4F5054494F4E03143Q0062752Q746F6E436C69636B65647C636F6E66696703113Q00646973706C617942544B4F7074696F6E7303173Q0062752Q746F6E436C69636B65647C62746B636F6E66696703073Q006F7665726D7367030F3Q00606320436F6E666967204F70656E20030F3Q0068616E646C6542544B436F6E666967022E3Q002659012Q00070001000100043A012Q00070001002030000200010002001271010400036Q00020004000200062D0002001B0001000100043A012Q001B0001002030000200010002001271010400046Q00020004000200062D0002001B0001000100043A012Q001B0001002030000200010002001271010400056Q00020004000200062D0002001B0001000100043A012Q001B0001002030000200010002001271010400066Q00020004000200062D0002001B0001000100043A012Q001B0001002030000200010002001271010400076Q00020004000200068C0102002000013Q00043A012Q002000010012FA000200084Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q002D0001002030000200010002001271010400096Q00020004000200068C0102002D00013Q00043A012Q002D00010012FA0002000A3Q0012710103000B4Q00440102000200010012FA0002000C4Q0058000300014Q00440102000200012Q0005010200014Q0099000200024Q00573Q00017Q00243Q00030A3Q0073686F77652Q66656374026Q00F03F030E3Q00416374697661746562746B6C6F67030F3Q00416374697661746566616B656C6F6703073Q0057692Q6E65723103063Q004368616E643103123Q0041637469766174657061746866696E64657203133Q004163746976617761726E696E676F6E6A6F696E03143Q004163746976617761726E696E676F6E6A6F696E32030D3Q00416374697661636F6E76657274030A3Q004163746976616661737403063Q00652Q666563742Q0103073Q00776562682Q6F6B03073Q0066616B656C6F6703073Q007761726E696E6703083Q007761726E696E673203053Q006175746F6303043Q0066617374030B3Q00416374697661636F6C656B030A3Q004163746976616E616D65028Q00030E3Q004163746976617370692Q6E616D6503133Q00416374697661746567656D73636865636B6572030D3Q00616374697661636F6E736F6C6503063Q007370616D6C770100030C3Q006163746976617370616D6C7703073Q007370696E616D6503103Q0041637469766174656175746F62616E3103103Q0041637469766174656175746F62616E3203103Q0041637469766174656175746F62616E3303103Q0041637469766174656175746F62616E3403103Q0041637469766174656175746F62616E3503103Q0041637469766174656175746F62616E3603153Q0041637469766174656175746F62616E66696E616C6500234Q008B014Q001800304Q0001000200304Q0003000200304Q0004000200304Q0005000200304Q0006000200304Q0007000200304Q0008000200304Q0009000200304Q000A000200302B3Q000B000200302B3Q000C000D00302B3Q000E000D00302B3Q000F000D00302B3Q0010000D00302B3Q0011000D00302B3Q0012000D00302B3Q0013000D00302B3Q0014000200302B3Q0015001600302B3Q0017000200302B3Q0018000200302B3Q0019001600302B3Q001A001B00302B3Q001C001600302B3Q001D000D00302B3Q001E001600302B3Q001F001600302B3Q0020001600302B3Q0021001600302B3Q0022001600302B3Q0023001600302B3Q002400162Q00993Q00024Q00573Q00017Q002E3Q00030A3Q0073686F77652Q66656374030E3Q00416374697661746562746B6C6F67030F3Q00416374697661746566616B656C6F6703073Q0057692Q6E65723103063Q004368616E643103123Q0041637469766174657061746866696E64657203133Q004163746976617761726E696E676F6E6A6F696E03143Q004163746976617761726E696E676F6E6A6F696E32030D3Q00416374697661636F6E76657274030A3Q004163746976616661737403063Q00652Q6665637403073Q00776562682Q6F6B03073Q0066616B656C6F6703073Q007761726E696E6703083Q007761726E696E673203053Q006175746F6303043Q0066617374030B3Q00416374697661636F6C656B030A3Q004163746976616E616D65030E3Q004163746976617370692Q6E616D6503133Q00416374697661746567656D73636865636B6572030D3Q00616374697661636F6E736F6C6503063Q007370616D6C77030C3Q006163746976617370616D6C7703073Q007370696E616D6503103Q0041637469766174656175746F62616E3103103Q0041637469766174656175746F62616E3203103Q0041637469766174656175746F62616E3303103Q0041637469766174656175746F62616E3403103Q0041637469766174656175746F62616E3503103Q0041637469766174656175746F62616E3603153Q0041637469766174656175746F62616E66696E616C6503023Q00696F03043Q006F70656E03153Q00776176655F70726F78795F636F6E6669672E74787403013Q007703053Q00706169727303053Q00777269746503013Q003D03083Q00746F737472696E6703013Q000A03053Q00636C6F73652Q033Q006C6F6703233Q006032436F6E66696775726174696F6E2073617665642073752Q63652Q7366752Q6C792103133Q00646973706C6179436F6E666967537461747573031F3Q0060344661696C656420746F207361766520636F6E66696775726174696F6E2100654Q007C014Q001800122Q000100013Q00104Q0001000100122Q000100023Q00104Q0002000100122Q000100033Q00104Q0003000100122Q000100043Q00104Q0004000100122Q000100053Q00107A3Q0005000100122Q000100063Q00104Q0006000100122Q000100073Q00104Q0007000100122Q000100083Q00104Q0008000100122Q000100093Q00104Q0009000100122Q0001000A3Q00107A3Q000A000100122Q0001000B3Q00104Q000B000100122Q0001000C3Q00104Q000C000100122Q0001000D3Q00104Q000D000100122Q0001000E3Q00104Q000E000100122Q0001000F3Q00107A3Q000F000100122Q000100103Q00104Q0010000100122Q000100113Q00104Q0011000100122Q000100123Q00104Q0012000100122Q000100133Q00104Q0013000100122Q000100143Q00107A3Q0014000100122Q000100153Q00104Q0015000100122Q000100163Q00104Q0016000100122Q000100173Q00104Q0017000100122Q000100183Q00104Q0018000100122Q000100193Q00107A3Q0019000100122Q0001001A3Q00104Q001A000100122Q0001001B3Q00104Q001B000100122Q0001001C3Q00104Q001C000100122Q0001001D3Q00104Q001D000100122Q0001001E3Q00101D012Q001E00010012FA0001001F3Q00101D012Q001F00010012FA000100203Q00101D012Q0020000100121F2Q0100213Q00202Q00010001002200122Q000200233Q00122Q000300246Q00010003000200062Q0001005F00013Q00043A012Q005F00010012FA000200254Q005800036Q004701020002000400043A012Q005500010020300007000100262Q0058000900053Q001271010A00273Q0012FA000B00284Q0058000C00064Q00C6000B00020002001271010C00294Q006F01090009000C2Q00EA0007000900010006140102004C0001000200043A012Q004C000100203000020001002A2Q00440102000200010012FA0002002B3Q0012710103002C4Q00440102000200010012FA0002002D4Q006200020001000100043A012Q006400010012FA0002002B3Q0012710103002E4Q00440102000200010012FA0002002D4Q00620002000100012Q00573Q00017Q00293Q0003023Q00696F03043Q006F70656E03153Q00776176655F70726F78795F636F6E6669672E74787403013Q007203053Q006C696E657303053Q006D6174636803093Q00282E2B293D282E2B2903043Q00747275652Q0103053Q0066616C7365010003083Q00746F6E756D62657203053Q00636C6F736503053Q00706169727303023Q005F472Q033Q006C6F6703243Q006032436F6E66696775726174696F6E206C6F616465642073752Q63652Q7366752Q6C7921030A3Q0045646974546F2Q676C65030A3Q005061746846696E64657203123Q0041637469766174657061746866696E646572026Q00F03F030B3Q0047656D73436865636B657203133Q00416374697661746567656D73636865636B657203083Q0048656E63686D616E03103Q0041637469766174656175746F62616E3103093Q004372696D655761766503103Q0041637469766174656175746F62616E32030E3Q0050737963686F74696342752Q6E7903103Q0041637469766174656175746F62616E3303113Q00506574547261696E657257686973746C6503103Q0041637469766174656175746F62616E34030D3Q0044617352656442612Q6C2Q6F6E03103Q0041637469766174656175746F62616E3503083Q00536E6F7742612Q6C03103Q0041637469766174656175746F62616E3603123Q004175746F42616E436F6E73756D61626C657303153Q0041637469766174656175746F62616E66696E616C6503133Q00646973706C6179436F6E666967537461747573033F3Q0060344E6F20736176656420636F6E66696775726174696F6E20666F756E642E204372656174696E672064656661756C7420636F6E66696775726174696F6E2E03133Q0063726561746544656661756C74436F6E666967030A3Q0073617665436F6E666967008D3Q00121F012Q00013Q00206Q000200122Q000100033Q00122Q000200048Q0002000200064Q007B00013Q00043A012Q007B00012Q00102Q015Q00203000023Q00052Q004701020002000400043A012Q00210001002030000600050006001271010800074Q00F500060008000700068C0106002100013Q00043A012Q0021000100068C0107002100013Q00043A012Q00210001002659010700160001000800043A012Q001600010020DB00010006000900043A012Q002100010026590107001A0001000A00043A012Q001A00010020DB00010006000B00043A012Q002100010012FA0008000C4Q0058000900074Q00C600080002000200062D000800200001000100043A012Q002000012Q0058000800074Q003B2Q01000600080006140102000B0001000100043A012Q000B000100203000023Q000D2Q00440102000200010012FA0002000E4Q0058000300014Q004701020002000400043A012Q002B00010012FA0007000F4Q003B010700050006000614010200290001000200043A012Q002900010012FA000200103Q001271010300114Q00440102000200010012FA000200123Q001271010300133Q0012FA000400143Q00265B000400360001001500043A012Q003600012Q004F00046Q0005010400014Q005F00020004000100122Q000200123Q00122Q000300163Q00122Q000400173Q00262Q0004003E0001001500043A012Q003E00012Q004F00046Q0005010400014Q005F00020004000100122Q000200123Q00122Q000300183Q00122Q000400193Q00262Q000400460001001500043A012Q004600012Q004F00046Q0005010400014Q005F00020004000100122Q000200123Q00122Q0003001A3Q00122Q0004001B3Q00262Q0004004E0001001500043A012Q004E00012Q004F00046Q0005010400014Q005F00020004000100122Q000200123Q00122Q0003001C3Q00122Q0004001D3Q00262Q000400560001001500043A012Q005600012Q004F00046Q0005010400014Q005F00020004000100122Q000200123Q00122Q0003001E3Q00122Q0004001F3Q00262Q0004005E0001001500043A012Q005E00012Q004F00046Q0005010400014Q005F00020004000100122Q000200123Q00122Q000300203Q00122Q000400213Q00262Q000400660001001500043A012Q006600012Q004F00046Q0005010400014Q005F00020004000100122Q000200123Q00122Q000300223Q00122Q000400233Q00262Q0004006E0001001500043A012Q006E00012Q004F00046Q0005010400014Q005F00020004000100122Q000200123Q00122Q000300243Q00122Q000400253Q00262Q000400760001001500043A012Q007600012Q004F00046Q0005010400014Q00EA0002000400010012FA000200264Q006200020001000100043A012Q008C00010012FA000100103Q0012A2000200276Q00010002000100122Q000100286Q00010001000200122Q0002000E6Q000300016Q00020002000400044Q008600010012FA0007000F4Q003B010700050006000614010200840001000200043A012Q008400010012FA000200294Q00620002000100010012FA000200264Q00620002000100012Q00573Q00017Q000E3Q00027Q004003043Q0066696E64031B3Q00616374696F6E7C696E7075740A7C746578747C2F63666773617665030A3Q0073617665436F6E66696703073Q006F7665726D736703143Q006063436F6E6669672050726F7879205361766564031B3Q00616374696F6E7C696E7075740A7C746578747C2F6366676C6F6164030A3Q006C6F6164436F6E66696703153Q006063436F6E6669672050726F7879204C6F6164656403183Q0062752Q746F6E436C69636B65647C636F6E6669677361766503153Q00606320436F6E6669672050726F787920536176656403133Q00646973706C6179436F6E66696753746174757303183Q0062752Q746F6E436C69636B65647C636F6E6669676C6F616403163Q00606320436F6E6669672050726F7879204C6F61646564023C3Q002659012Q000F0001000100043A012Q000F0001002030000200010002001271010400036Q00020004000200068C0102000F00013Q00043A012Q000F00010012FA000200044Q000401020001000100122Q000200053Q00122Q000300066Q0002000200014Q000200016Q000200023Q00044Q003B0001002659012Q001E0001000100043A012Q001E0001002030000200010002001271010400076Q00020004000200068C0102001E00013Q00043A012Q001E00010012FA000200084Q000401020001000100122Q000200053Q00122Q000300096Q0002000200014Q000200016Q000200023Q00044Q003B00010020300002000100020012710104000A6Q00020004000200068C0102002D00013Q00043A012Q002D00010012FA000200053Q00123C0003000B6Q00020002000100122Q0002000C6Q00020001000100122Q000200046Q0002000100014Q000200016Q000200023Q00043A012Q003B00010020300002000100020012710104000D6Q00020004000200068C0102003B00013Q00043A012Q003B00010012FA000200053Q00123C0003000E6Q00020002000100122Q0002000C6Q00020001000100122Q000200086Q0002000100014Q000200016Q000200024Q00573Q00017Q00393Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F03BF3Q007365745F64656661756C745F636F6C6F727C606F0A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6063576176652050726F787920436F6E66696775726174696F6E205374617475734Q607C6C6566747C33327C0A612Q645F7370616365727C736D612Q6C7C0A612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C602143752Q72656E7420436F6E66696775726174696F6E3A7C6C6566747C37312Q387C0A612Q645F7370616365727C736D612Q6C7C0A032B3Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C603953686F7720652Q66656374733A20030A3Q0073686F77652Q6665637403043Q0060324F4E03053Q0060344F2Q4603073Q007C6C6566747C0A03263Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C603942544B206C6F673A20030E3Q00416374697661746562746B6C6F67032C3Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C603946616B65205370696E206C6F673A20030F3Q00416374697661746566616B656C6F67032F3Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F2044726F702057692Q6E65723A2003073Q0057692Q6E657231032D3Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F20507574204368616E643A2003063Q004368616E643103293Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60395061746846696E6465723A2003123Q0041637469766174657061746866696E64657203363Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60395761726E696E67204D652Q73616765204F6E204A6F696E3A2003133Q004163746976617761726E696E676F6E6A6F696E032E3Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394D652Q73616765204F6E204A6F696E3A2003143Q004163746976617761726E696E676F6E6A6F696E3203303Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F20436F6E76657274204C6F636B3A20030D3Q00416374697661636F6E7665727403283Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C603946617374204D6F64653A20030A3Q004163746976616661737403293Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C6039436F6C656B204D6F64653A20030B3Q00416374697661636F6C656B03283Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394E616D65204D6F64653A20030A3Q004163746976616E616D6503323Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394C617374205370696E204E616D65204D6F64653A20030E3Q004163746976617370692Q6E616D65032B3Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C603947656D7320436865636B65723A2003133Q00416374697661746567656D73636865636B657203303Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C6039436F6E736F6C652057617465726D61726B3A20030D3Q00616374697661636F6E736F6C6503283Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60395370616D204D6F64653A20030C3Q006163746976617370616D6C7703303Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F2042616E2048656E63686D616E3A2003103Q0041637469766174656175746F62616E3103313Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F2042616E204372696D65576176653A2003103Q0041637469766174656175746F62616E3203363Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F2042616E2050737963686F74696342752Q6E793A2003103Q0041637469766174656175746F62616E3303393Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F2042616E20506574547261696E657257686973746C653A2003103Q0041637469766174656175746F62616E3403353Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F2042616E2044617352656442612Q6C2Q6F6E3A2003103Q0041637469766174656175746F62616E3503303Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F2042616E20536E6F7742612Q6C3A2003103Q0041637469766174656175746F62616E3603333Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394175746F2042616E20436F6E73756D61626C65733A2003153Q0041637469766174656175746F62616E66696E616C65033A3Q00612Q645F7370616365727C736D612Q6C7C0A656E645F6469616C6F677C636F6E6669676469616C6F677C436C6F73657C4F6B61797C0A4Q20030B3Q0053656E645661726C69737400DA4Q0010016Q00302B3Q0001000200302B3Q000300040012712Q0100063Q001271010200073Q0012FA000300083Q0026590103000B0001000500043A012Q000B0001001271010300093Q00062D0003000C0001000100043A012Q000C00010012710103000A3Q0012710104000B3Q0012710105000C3Q0012FA0006000D3Q002659010600140001000500043A012Q00140001001271010600093Q00062D000600150001000100043A012Q001500010012710106000A3Q0012710107000B3Q0012710108000E3Q0012FA0009000F3Q0026590109001D0001000500043A012Q001D0001001271010900093Q00062D0009001E0001000100043A012Q001E00010012710109000A3Q001271010A000B3Q001271010B00103Q0012FA000C00113Q002659010C00260001000500043A012Q00260001001271010C00093Q00062D000C00270001000100043A012Q00270001001271010C000A3Q001271010D000B3Q001271010E00123Q0012FA000F00133Q002659010F002F0001000500043A012Q002F0001001271010F00093Q00062D000F00300001000100043A012Q00300001001271010F000A3Q0012710110000B3Q001271011100143Q0012FA001200153Q002659011200380001000500043A012Q00380001001271011200093Q00062D001200390001000100043A012Q003900010012710112000A3Q0012710113000B3Q001271011400163Q0012FA001500173Q002659011500410001000500043A012Q00410001001271011500093Q00062D001500420001000100043A012Q004200010012710115000A3Q0012710116000B3Q001271011700183Q0012FA001800193Q0026590118004A0001000500043A012Q004A0001001271011800093Q00062D0018004B0001000100043A012Q004B00010012710118000A3Q0012710119000B3Q001271011A001A3Q0012FA001B001B3Q002659011B00530001000500043A012Q00530001001271011B00093Q00062D001B00540001000100043A012Q00540001001271011B000A3Q001271011C000B3Q001271011D001C3Q0012FA001E001D3Q002659011E005C0001000500043A012Q005C0001001271011E00093Q00062D001E005D0001000100043A012Q005D0001001271011E000A3Q001271011F000B3Q0012710120001E3Q0012FA0021001F3Q002659012100650001000500043A012Q00650001001271012100093Q00062D002100660001000100043A012Q006600010012710121000A3Q0012710122000B3Q001271012300203Q0012FA002400213Q0026590124006E0001000500043A012Q006E0001001271012400093Q00062D0024006F0001000100043A012Q006F00010012710124000A3Q0012710125000B3Q001271012600223Q0012FA002700233Q002659012700770001000500043A012Q00770001001271012700093Q00062D002700780001000100043A012Q007800010012710127000A3Q0012710128000B3Q001271012900243Q0012FA002A00253Q002659012A00800001000500043A012Q00800001001271012A00093Q00062D002A00810001000100043A012Q00810001001271012A000A3Q001271012B000B3Q001271012C00263Q0012FA002D00273Q002659012D00890001000500043A012Q00890001001271012D00093Q00062D002D008A0001000100043A012Q008A0001001271012D000A3Q001271012E000B3Q001271012F00283Q0012FA003000293Q002659013000920001000500043A012Q00920001001271013000093Q00062D003000930001000100043A012Q009300010012710130000A3Q0012710131000B3Q0012710132002A3Q0012FA0033002B3Q0026590133009B0001000500043A012Q009B0001001271013300093Q00062D0033009C0001000100043A012Q009C00010012710133000A3Q0012710134000B3Q0012710135002C3Q0012FA0036002D3Q002659013600A40001000500043A012Q00A40001001271013600093Q00062D003600A50001000100043A012Q00A500010012710136000A3Q0012710137000B3Q0012710138002E3Q0012FA0039002F3Q002659013900AD0001000500043A012Q00AD0001001271013900093Q00062D003900AE0001000100043A012Q00AE00010012710139000A3Q001271013A000B3Q001271013B00303Q0012FA003C00313Q002659013C00B60001000500043A012Q00B60001001271013C00093Q00062D003C00B70001000100043A012Q00B70001001271013C000A3Q001271013D000B3Q001271013E00323Q0012FA003F00333Q002659013F00BF0001000500043A012Q00BF0001001271013F00093Q00062D003F00C00001000100043A012Q00C00001001271013F000A3Q0012710140000B3Q001271014100343Q0012FA004200353Q002659014200C80001000500043A012Q00C80001001271014200093Q00062D004200C90001000100043A012Q00C900010012710142000A3Q0012710143000B3Q001271014400363Q0012FA004500373Q002659014500D10001000500043A012Q00D10001001271014500093Q00062D004500D20001000100043A012Q00D200010012710145000A3Q0012710146000B3Q001271014700384Q00802Q010001004700104Q0005000100122Q000100396Q00028Q0001000200016Q00017Q00043Q00027Q004003043Q0066696E64031D3Q00616374696F6E7C696E7075740A7C746578747C2F63666773746174757303133Q00646973706C6179436F6E666967537461747573020C3Q002659012Q000B0001000100043A012Q000B0001002030000200010002001271010400036Q00020004000200068C0102000B00013Q00043A012Q000B00010012FA000200044Q00620002000100012Q0005010200014Q0099000200024Q00573Q00017Q00253Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF03023Q006F7303043Q006461746503053Q0025483A254D026Q00F03F03153Q000A7365745F64656661756C745F636F6C6F727C606F03343Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C606340576176652050726F7879204Q607C6C6566747C33327C03463Q000A612Q645F696D6167655F62752Q746F6E7C62612Q6E65727C63616368652F696E746572666163652F6C617267652F62612Q6E65722E722Q7465787C6E6F666C6167733Q7C03123Q000A612Q645F7370616365727C736D612Q6C7C03213Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603048652Q6C6F2003083Q004765744C6F63616C03043Q006E616D65030B3Q007C6C6566747C363237387C03233Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6030576F726C64203A2003083Q00476574576F726C64030B3Q00207C6C6566747C3237387C03273Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6030446174652054696D65203A2003203Q000A612Q645F746578745F696E7075747C73652Q746578747C6032546578743A7C03083Q007370616D7465787403053Q007C3132307C03273Q000A612Q645F746578745F696E7075747C73657464656C61797C603244656C617920286D73293A7C03093Q007370616D64656C617903043Q007C31307C031C3Q000A612Q645F637573746F6D5F6D617267696E7C783A303B793A31307C03303Q000A612Q645F636865636B626F787C5374617274205370616D7C603241637469766174652060394175746F205370616D7C03093Q0073746172747370616D03013Q007C031D3Q000A612Q645F637573746F6D5F6D617267696E7C783A303B793A2D33327C034E3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C204163746976617465204175746F205370616D7C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C03373Q000A612Q645F636865636B626F787C5769746820456D6F7469636F6E7C603241637469766174652060395769746820456D6F7469636F6E7C03113Q007370616D77697468656D6F7469636F6E73035C3Q000A612Q645F637573746F6D5F74657874626F787C602157692Q6C2044697361626C6564202D20456E61626C6564205769746820456D6F7469636F6E7C73697A653A74696E793B636F6C6F723A3139332C3230322C322Q352C322Q307C031F3Q000A656E645F6469616C6F677C7365747370616D746578742Q7C412Q706C797C030B3Q0053656E645661726C69737400324Q0053016Q00304Q0001000200304Q0003000400122Q000100053Q00202Q00010001000600122Q000200076Q00010002000200122Q000200093Q00122Q0003000A3Q00122Q0004000B3Q0012710105000C3Q0012D00006000D3Q00122Q0007000E6Q00070001000200202Q00070007000F00122Q000800103Q00122Q000900113Q00122Q000A00126Q000A0001000200202Q000A000A000F00122Q000B00133Q001271010C00144Q00A5010D00013Q00122Q000E00133Q00122Q000F000C3Q00122Q001000153Q00122Q001100163Q00122Q001200173Q00122Q001300183Q00122Q001400193Q00122Q0015001A3Q00122Q0016001B3Q0012710117001C3Q0012140018001D3Q00122Q0019001E3Q00122Q001A001F3Q00122Q001B00203Q00122Q001C001B3Q00122Q001D00213Q00122Q001E00223Q00122Q001F001E3Q00122Q0020001F3Q00122Q002100233Q001271012200244Q008001020002002200104Q0008000200122Q000200256Q00038Q0002000200016Q00017Q00243Q0003043Q0067737562032C3Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C7365747370616D74657874034Q0003013Q000A03083Q0073652Q746578747C03053Q006D61746368030E3Q0073657464656C61797C2825642B2903093Q007370616D64656C617903103Q005374617274205370616D7C2825642B2903013Q003003133Q005769746820456D6F7469636F6E7C2825642B2903083Q007370616D74657874030C3Q0073657464656C61797C25642B030E3Q005374617274205370616D7C25642B03113Q005769746820456D6F7469636F6E7C25642B03083Q00746F6E756D62657203093Q0073746172747370616D030C3Q0077697468656D6F7469636F6E03113Q007370616D77697468656D6F7469636F6E732Q033Q006C6F67031E3Q00603953752Q63652Q7366752Q6C7920736574207465787420746F3A603020031F3Q00603953752Q63652Q7366752Q6C79207365742064656C617920746F3A6030202Q033Q00206D73026Q00F03F03053Q007370616D3203073Q006F7665726D7367031B3Q0060395374617274205370616D2073657420746F3A60322074727565030A3Q0053656E645061636B6574027Q004003393Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2060655370616D2053657420546F2060324F6E028Q00031C3Q0060395374617274205370616D2073657420746F3A60342066616C7365033A3Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2060655370616D2053657420546F2060344F2Q6603113Q007370616D77697468656D6F7469636F6E31031E3Q0060395769746820456D6F7469636F6E2073657420746F3A60322074727565031F3Q0060395769746820456D6F7469636F6E2073657420746F3A60342066616C7365016F3Q00203000013Q0001001271010300023Q001271010400034Q00C800010004000200202Q00010001000100122Q000300043Q00122Q000400036Q00010004000200202Q00010001000100122Q000300053Q00122Q000400036Q00010004000200202Q00023Q0006001271010400076Q00020004000200062D000200120001000100043A012Q001200010012FA000200083Q00203000033Q0006001271010500096Q00030005000200062D000300180001000100043A012Q001800010012710103000A3Q00203000043Q00060012710106000B6Q00040006000200062D0004001E0001000100043A012Q001E00010012710104000A3Q0020300005000100010012710107000D3Q001271010800036Q0005000800020020300005000500010012710107000E3Q001271010800036Q0005000800020020300005000500010012710107000F3Q001271010800036Q00050008000200120A0005000C3Q0012FA000500104Q0058000600024Q00C600050002000200120A000500083Q0012FA000500104Q0058000600034Q00C600050002000200120A000500113Q0012FA000500104Q0058000600044Q00C600050002000200120A000500123Q0012FA000500104Q0058000600044Q00C600050002000200120A000500133Q0012FA000500143Q001271010600153Q0012FA0007000C4Q006F0106000600072Q00440105000200010012FA000500143Q001271010600163Q0012FA000700083Q001271010800174Q006F0106000600082Q00440105000200010012FA000500113Q002659010500520001001800043A012Q005200012Q0005010500013Q00120A000500193Q0012FA0005001A3Q0012710106001B4Q00440105000200010012FA0005001C3Q0012710106001D3Q0012710107001E4Q00EA0005000700010012FA000500113Q0026590105005E0001001F00043A012Q005E00012Q000501055Q00120A000500193Q0012FA0005001A3Q001271010600204Q00440105000200010012FA0005001C3Q0012710106001D3Q001271010700214Q00EA0005000700010012FA000500123Q002659010500660001001800043A012Q006600012Q0005010500013Q00120A000500223Q0012FA000500143Q001271010600234Q00440105000200010012FA000500123Q0026590105006E0001001F00043A012Q006E00012Q000501055Q00120A000500223Q0012FA000500143Q001271010600244Q00440105000200012Q00573Q00017Q00113Q0003113Q007370616D77697468656D6F7469636F6E3103053Q00536C2Q6570025Q00408F4003093Q00656D6F7469636F6E73026Q00F03F030A3Q0053656E645061636B6574027Q004003133Q00616374696F6E7C696E7075740A7C746578747C03063Q002060623A206003043Q006D61746803063Q0072616E646F6D026Q000840026Q002240034Q0003083Q007370616D7465787403143Q00616374696F6E7C696E7075740A7C746578747C6003093Q007370616D64656C617901313Q0012FA000100013Q00068C2Q01001B00013Q00043A012Q001B00010012FA000100023Q001271010200034Q00442Q01000200010012FA000100043Q0012FA000200044Q007F010200024Q009F00023Q00020020790102000200052Q00840001000100020012FA000200063Q001271010300073Q001271010400084Q0058000500013Q001271010600093Q0012FA0007000A3Q0020CC00070007000B0012710108000C3Q0012710109000D6Q0007000900020012710108000E3Q0012FA0009000F4Q006F0104000400092Q00EA00020004000100043A012Q002D00010012FA000100013Q00062D0001002D0001000100043A012Q002D00010012FA000100023Q001229000200036Q00010002000100122Q000100063Q00122Q000200073Q00122Q000300103Q00122Q0004000A3Q00202Q00040004000B00122Q0005000C3Q00122Q0006000D6Q0004000600020012710105000E3Q0012FA0006000F4Q006F0103000300062Q00EA0001000300010012FA000100023Q0012FA000200114Q00442Q01000200012Q00573Q00017Q00083Q00027Q004003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F73657403173Q00616374696F6E7C696E7075740A7C746578747C2F53455403153Q0062752Q746F6E436C69636B65647C7370616D65723003143Q00646973706C61795370616D5365744469616C6F67032C3Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C7365747370616D7465787403193Q0068616E646C655365745370616D54657874416E6444656C617902213Q002659012Q00160001000100043A012Q00160001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102001600013Q00043A012Q001600010012FA000200064Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q00200001002030000200010002001271010400076Q00020004000200068C0102002000013Q00043A012Q002000010012FA000200084Q0058000300014Q00440102000200012Q0005010200014Q0099000200024Q00573Q00017Q00103Q00027Q004003043Q0066696E6403183Q00616374696F6E7C696E7075740A7C746578747C2F7370616D03183Q00616374696F6E7C696E7075740A7C746578747C2F5350414D03153Q0062752Q746F6E436C69636B65647C7370616D65723103053Q007370616D3203073Q006F7665726D736703123Q006034205350414D2044454143544956415445030A3Q0053656E645061636B6574033B3Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2060655350414D206034444541435449564154452003093Q0073746172747370616D028Q0003113Q007370616D77697468656D6F7469636F6E7303103Q006034205350414D20414354495641544503393Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2060655350414D206032414354495641544520026Q00F03F02323Q000E240001000700013Q00043A012Q00070001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102003100013Q00043A012Q003100010012FA000200063Q00068C0102002200013Q00043A012Q002200012Q000501025Q001219010200063Q00122Q000200073Q00122Q000300086Q00020002000100122Q000200093Q00122Q000300013Q00122Q0004000A6Q00020004000100122Q0002000C3Q00122Q0002000B3Q00122Q0002000C3Q00122Q0002000D3Q00044Q002F00012Q0005010200013Q00120A000200063Q0012FA000200073Q0012710103000E4Q00440102000200010012FA000200093Q001271010300013Q0012710104000F4Q00EA000200040001001271010200103Q00120A0002000B3Q001271010200103Q00120A0002000D4Q0005010200014Q0099000200024Q00573Q00017Q000C3Q00030A3Q007374617274436F756E74028Q0003083Q00656E64436F756E74026Q00344003073Q0064656C61795342026Q00084003083Q0074696D655A6F6E65026Q001C4003063Q0074657874534203153Q004155544F20534220425920574156452050524F585903053Q00616473534203103Q00606323574156452050524F585920534200094Q00A65Q000600304Q0001000200304Q0003000400304Q0005000600304Q0007000800304Q0009000A00304Q000B000C6Q00028Q00017Q00123Q0003023Q00696F03043Q006F70656E03143Q0062726F6164636173745F636F6E6669672E74787403013Q007703053Q00777269746503063Q00737472696E6703063Q00666F726D6174030E3Q007374617274436F756E743D25640A030C3Q00656E64436F756E743D25640A030D3Q0064656C617953423D252E31660A030C3Q0074696D655A6F6E653D25640A030A3Q007465787453423D25730A03093Q0061647353423D25730A03053Q00636C6F73652Q033Q006C6F67032D3Q00603242726F61646361737420636F6E66696775726174696F6E2073617665642073752Q63652Q7366752Q6C792103143Q00646973706C6179436F6E6669675374617475733103293Q0060344661696C656420746F20736176652062726F61646361737420636F6E66696775726174696F6E21003F3Q00121F012Q00013Q00206Q000200122Q000100033Q00122Q000200048Q0002000200064Q003900013Q00043A012Q0039000100203000013Q0005001288000300063Q00202Q00030003000700122Q000400086Q00058Q000300056Q00013Q000100202Q00013Q000500122Q000300063Q00202Q00030003000700122Q000400096Q000500016Q000300056Q00013Q000100202Q00013Q000500122Q000300063Q00202Q00030003000700122Q0004000A6Q000500026Q000300056Q00013Q000100202Q00013Q000500122Q000300063Q00202Q00030003000700122Q0004000B6Q000500036Q000300056Q00013Q000100202Q00013Q000500122Q000300063Q00202Q00030003000700122Q0004000C6Q000500046Q000300056Q00013Q000100202Q00013Q000500122Q000300063Q00202Q00030003000700122Q0004000D6Q000500056Q000300056Q00013Q000100202Q00013Q000E4Q00010002000100122Q0001000F3Q00122Q000200106Q00010002000100122Q000100116Q00010001000100044Q003E00010012FA0001000F3Q001271010200124Q00442Q01000200010012FA000100114Q00620001000100012Q00573Q00017Q00173Q0003023Q00696F03043Q006F70656E03143Q0062726F6164636173745F636F6E6669672E74787403013Q007203053Q006C696E657303053Q006D6174636803093Q00282E2B293D282E2B29030A3Q007374617274436F756E7403083Q00746F6E756D62657203083Q00656E64436F756E7403073Q0064656C6179534203083Q0074696D655A6F6E6503063Q0074657874534203053Q00616473534203053Q00636C6F73652Q033Q006C6F67032E3Q00603242726F61646361737420636F6E66696775726174696F6E206C6F616465642073752Q63652Q7366752Q6C792103143Q00646973706C6179436F6E6669675374617475733103493Q0060344E6F2073617665642062726F61646361737420636F6E66696775726174696F6E20666F756E642E204372656174696E672064656661756C7420636F6E66696775726174696F6E2E03143Q0063726561746544656661756C74436F6E6669673103053Q00706169727303023Q005F4703133Q007361766542726F616463617374436F6E66696700503Q00121F012Q00013Q00206Q000200122Q000100033Q00122Q000200048Q0002000200064Q003E00013Q00043A012Q003E000100203000013Q00052Q00472Q010002000300043A012Q00340001002030000500040006001271010700074Q00F500050007000600068C0105003400013Q00043A012Q0034000100068C0106003400013Q00043A012Q00340001002659010500180001000800043A012Q001800010012FA000700094Q0058000800064Q00C60007000200022Q001A00075Q00043A012Q003400010026590105001F0001000A00043A012Q001F00010012FA000700094Q0058000800064Q00C60007000200022Q001A000700013Q00043A012Q00340001002659010500260001000B00043A012Q002600010012FA000700094Q0058000800064Q00C60007000200022Q001A000700023Q00043A012Q003400010026590105002D0001000C00043A012Q002D00010012FA000700094Q0058000800064Q00C60007000200022Q001A000700033Q00043A012Q00340001002659010500310001000D00043A012Q003100012Q001A000600043Q00043A012Q00340001002659010500340001000E00043A012Q003400012Q001A000600053Q0006142Q01000A0001000100043A012Q000A000100203000013Q000F2Q00442Q01000200010012FA000100103Q001271010200114Q00442Q01000200010012FA000100124Q006200010001000100043A012Q004F00010012FA000100103Q0012A2000200136Q00010002000100122Q000100146Q00010001000200122Q000200156Q000300016Q00020002000400044Q004900010012FA000700164Q003B010700050006000614010200470001000200043A012Q004700010012FA000200124Q00620002000100010012FA000200174Q00620002000100012Q00573Q00017Q00263Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F03153Q000A7365745F64656661756C745F636F6C6F727C606F033C3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C606340576176652042726F61646361737420436F6E6669677C6C6566747C323438307C03463Q000A612Q645F696D6167655F62752Q746F6E7C62612Q6E65727C63616368652F696E746572666163652F6C617267652F62612Q6E65722E722Q7465787C6E6F666C6167733Q7C03213Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603048652Q6C6F2003083Q004765744C6F63616C03043Q006E616D65030B3Q007C6C6566747C363237387C03233Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6030576F726C64203A2003083Q00476574576F726C64030B3Q00207C6C6566747C3237387C03123Q000A612Q645F7370616365727C736D612Q6C7C034D3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C606357656C636F6D6520546F2054686520436F6E66696775726174696F6E732042726F6164636173747C6C6566747C323438307C032A3Q000A612Q645F746578745F696E7075747C7374617274436F756E747C6032537461727420436F756E743A7C03053Q007C3Q397C03263Q000A612Q645F746578745F696E7075747C656E64436F756E747C6032456E6420436F756E743A7C03043Q007C31307C03213Q000A612Q645F746578745F696E7075747C64656C617953427C603244656C61793A7C03253Q000A612Q645F746578745F696E7075747C74696D655A6F6E657C603254696D657A6F6E653A7C031F3Q000A612Q645F746578745F696E7075747C7465787453427C6032546578743A7C031D3Q000A612Q645F746578745F696E7075747C61647353427C60324164733A7C033A3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C606353746172742F53746F702042726F6164636173747C6C6566747C323438307C032A3Q000A746578745F7363616C696E675F737472696E677C696D6C2Q6F6B696E672Q73323Q73636F736F6C7C034D3Q000A612Q645F62752Q746F6E5F776974685F69636F6E7C7365747369676E7C60325772656E6368205369676E20546F2053657420546578747C73746174696359652Q6C6F774672616D657C33327C03473Q000A612Q645F62752Q746F6E5F776974685F69636F6E7C737461727473627C603253746172742042726F6164636173747C73746174696359652Q6C6F774672616D657C323438307C03453Q000A612Q645F62752Q746F6E5F776974685F69636F6E7C73746F7073627C603453746F702042726F6164636173747C73746174696359652Q6C6F774672616D657C323438307C032B3Q000A612Q645F62752Q746F6E5F776974685F69636F6E2Q7C454E445F4C4953547C6E6F666C6167737C302Q7C03253Q000A612Q645F62752Q746F6E7C7362636F6E6669677C6039412Q706C79204368616E6765737C03213Q000A612Q645F62752Q746F6E7C7362736176657C60395361766520436F6E6669677C03213Q000A612Q645F62752Q746F6E7C73626C6F61647C60394C6F616420436F6E6669677C032A3Q000A612Q645F62752Q746F6E7C73627374617475737C60395669657720436F6E666967205374617475737C03173Q000A612Q645F62752Q746F6E7C6261636B317C4261636B7C031B3Q000A656E645F6469616C6F677C636C6F73652Q7C6034436C6F73657C030B3Q0053656E645661726C69737400394Q0010016Q00302B3Q0001000200302B3Q000300040012712Q0100063Q001271010200073Q001271010300083Q0012D0000400093Q00122Q0005000A6Q00050001000200202Q00050005000B00122Q0006000C3Q00122Q0007000D3Q00122Q0008000E6Q00080001000200202Q00080008000B00122Q0009000F3Q001271010A00103Q001271010B00113Q001271010C00103Q001271010D00124Q00E1000E5Q00122Q000F00133Q00122Q001000146Q001100013Q00122Q001200153Q00122Q001300166Q001400023Q00122Q001500153Q00122Q001600176Q001700033Q001271011800153Q001271011900184Q0059001A00043Q001274011B00133Q00122Q001C00196Q001D00053Q00122Q001E00133Q00122Q001F00103Q00122Q0020001A3Q00122Q002100103Q00122Q0022001B3Q00122Q0023001C3Q00122Q0024001D3Q0012710125001E3Q00127B0126001F3Q00122Q002700203Q00122Q002800213Q00122Q002900223Q00122Q002A00233Q00122Q002B00243Q00122Q002C00256Q00010001002C00104Q0005000100122Q000100264Q005800026Q00442Q01000200012Q00573Q00017Q00183Q0003043Q006773756203293Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C7362636F6E666967034Q0003013Q000A03083Q0073652Q746578747C03083Q00746F6E756D62657203053Q006D6174636803103Q007374617274436F756E747C2825642B29030E3Q00656E64436F756E747C2825642B2903113Q0064656C617953427C285B2564252E5D2B2903063Q00737472696E6703063Q00666F726D617403043Q00252E3166030E3Q0074696D655A6F6E657C2825642B29030E3Q007465787453427C285B5E0A5D2B29030D3Q0061647353427C285B5E0A5D2B292Q033Q006C6F6703253Q00603953752Q63652Q7366752Q6C792073657420537461727420436F756E7420746F3A60302003233Q00603953752Q63652Q7366752Q6C792073657420456E6420436F756E7420746F3A603020031F3Q00603953752Q63652Q7366752Q6C79207365742044656C617920746F3A60302003083Q00206D696E75746573032A3Q00603953752Q63652Q7366752Q6C79207365742054696D657A6F6E6520746F3A6030205554432F474D542B031E3Q00603953752Q63652Q7366752Q6C7920736574205465787420746F3A603020031D3Q00603953752Q63652Q7366752Q6C79207365742041647320746F3A60302001663Q00203000013Q0001001271010300023Q001271010400036Q00010004000200209700010001000100122Q000300043Q00122Q000400036Q00010004000200202Q00010001000100122Q000300053Q00122Q000400036Q00010004000200122Q000200063Q00202Q00033Q0007001271010500084Q00A1000300054Q00C500023Q000200062D000200140001000100043A012Q001400012Q005900026Q001A00025Q001260000200063Q00202Q00033Q000700122Q000500096Q000300056Q00023Q000200062Q0002001D0001000100043A012Q001D00012Q0059000200014Q001A000200013Q001260000200063Q00202Q00033Q000700122Q0005000A6Q000300056Q00023Q000200062Q000200260001000100043A012Q002600012Q0059000200024Q001A000200023Q0012F9000200063Q00122Q0003000B3Q00202Q00030003000C00122Q0004000D6Q000500026Q000300056Q00023Q00024Q000200023Q00122Q000200063Q00202Q00033Q000700122Q0005000E6Q000300056Q00023Q000200062Q000200370001000100043A012Q003700012Q0059000200034Q001A000200033Q00203000023Q00070012710104000F6Q00020004000200062D0002003E0001000100043A012Q003E00012Q0059000200044Q001A000200043Q00203000023Q0007001271010400106Q00020004000200062D000200450001000100043A012Q004500012Q0059000200054Q001A000200053Q0012FA000200113Q001271010300124Q005900046Q006F0103000300042Q00440102000200010012FA000200113Q001271010300134Q0059000400014Q006F0103000300042Q00440102000200010012FA000200113Q0012A9000300146Q000400023Q00122Q000500156Q0003000300054Q00020002000100122Q000200113Q00122Q000300166Q000400036Q0003000300044Q0002000200010012FA000200113Q001271010300174Q0059000400044Q006F0103000300042Q00440102000200010012FA000200113Q001271010300184Q0059000400054Q006F0103000300042Q00440102000200012Q00573Q00017Q00103Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F03CB3Q007365745F64656661756C745F636F6C6F727C606F0A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6063576176652050726F78792042726F61646361737420436F6E66696775726174696F6E205374617475734Q607C6C6566747C323438307C0A612Q645F7370616365727C736D612Q6C7C0A612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C602143752Q72656E7420436F6E66696775726174696F6E3A7C6C6566747C37312Q387C0A612Q645F7370616365727C736D612Q6C7C0A032C3Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C6039537461727420436F756E743A20603203073Q007C6C6566747C0A032A3Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C6039456E6420436F756E743A20603203263Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C603944656C61793A206032030F3Q00206D696E757465737C6C6566747C0A03313Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C603954696D657A6F6E653A2060325554432F474D542B03253Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C6039546578743A20603203243Q00612Q645F6C6162656C5F776974685F69636F6E7C6D656469756D7C60394164733A206032033A3Q00612Q645F7370616365727C736D612Q6C7C0A656E645F6469616C6F677C636F6E6669676469616C6F677C436C6F73657C4F6B61797C0A4Q20030B3Q0053656E645661726C697374001D4Q0010016Q00302B3Q0001000200302B3Q000300040012712Q0100063Q001271010200074Q00E100035Q00122Q000400083Q00122Q000500096Q000600013Q00122Q000700083Q00122Q0008000A6Q000900023Q00122Q000A000B3Q00122Q000B000C6Q000C00033Q001271010D00083Q001271010E000D4Q0059000F00043Q001271011000083Q0012710111000E4Q0059001200053Q001271011300083Q0012710114000F4Q00802Q010001001400104Q0005000100122Q000100106Q00028Q0001000200016Q00017Q00113Q00027Q004003043Q0066696E6403163Q0062752Q746F6E436C69636B65647C7362636F6E66696703093Q00736574436F6E66696703143Q0062752Q746F6E436C69636B65647C73627361766503133Q007361766542726F616463617374436F6E66696703073Q006F7665726D736703183Q006063436F6E6669672042726F61646361737420536176656403143Q0062752Q746F6E436C69636B65647C73626C6F616403133Q006C6F616442726F616463617374436F6E66696703193Q006063436F6E6669672042726F616463617374204C6F6164656403063Q0073757065726203163Q0062752Q746F6E436C69636B65647C736273746174757303143Q00646973706C6179436F6E66696753746174757331031C3Q00616374696F6E7C696E7075740A7C746578747C2F7362737461747573031A3Q00616374696F6E7C696E7075740A7C746578747C2F736273617665031A3Q00616374696F6E7C696E7075740A7C746578747C2F73626C6F616402593Q002659012Q00580001000100043A012Q00580001002030000200010002001271010400036Q00020004000200068C0102000D00013Q00043A012Q000D00010012FA000200044Q0058000300014Q00440102000200012Q0005010200014Q0099000200023Q00043A012Q00580001002030000200010002001271010400056Q00020004000200068C0102001A00013Q00043A012Q001A00010012FA000200064Q000401020001000100122Q000200073Q00122Q000300086Q0002000200014Q000200016Q000200023Q00044Q00580001002030000200010002001271010400096Q00020004000200068C0102002900013Q00043A012Q002900010012FA0002000A4Q00620002000100010012FA000200073Q0012710103000B4Q00440102000200010012FA0002000C4Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q005800010020300002000100020012710104000D6Q00020004000200068C0102003300013Q00043A012Q003300010012FA0002000E4Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q005800010020300002000100020012710104000F6Q00020004000200068C0102003D00013Q00043A012Q003D00010012FA0002000E4Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q00580001002030000200010002001271010400106Q00020004000200068C0102004A00013Q00043A012Q004A00010012FA000200064Q000401020001000100122Q000200073Q00122Q000300086Q0002000200014Q000200016Q000200023Q00044Q00580001002030000200010002001271010400116Q00020004000200068C0102005800013Q00043A012Q005800010012FA0002000A4Q00620002000100010012FA0002000C4Q009300020001000100122Q000200073Q00122Q0003000B6Q0002000200014Q000200016Q000200024Q00573Q00017Q00073Q00030A3Q0053656E645061636B6574027Q004003123Q00616374696F6E7C696E7075740A746578747C03073Q007465787465746303153Q0020603442726F6164636173742073746F2Q7065642E03073Q006F7665726D736703143Q00603442726F6164636173742073746F2Q7065642E000D4Q0005017Q001A7Q0012FA3Q00013Q0012B5000100023Q00122Q000200033Q00122Q000300043Q00122Q000400056Q0002000200046Q000200010012FA3Q00063Q0012712Q0100074Q0044012Q000200012Q00573Q00017Q00043Q00027Q004003043Q0066696E64031C3Q00616374696F6E7C696E7075740A7C746578747C2F73746F706361737403143Q0062752Q746F6E436C69636B65647C73746F70736202113Q002659012Q00070001000100043A012Q00070001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102001000013Q00043A012Q001000012Q005900026Q00620002000100012Q0005010200014Q0099000200024Q00573Q00017Q001A3Q0003B93Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F313235373938312Q38373830353339353031342F31323632333130332Q39373638372Q382Q39322F7374616E646172645F352E6769663F65783D2Q363938633461622669733D2Q36392Q3733326226686D3D38636162333139666430386566393761633263376430373632666566363866633032343062372Q362Q3562643061332Q3239313836303364613566342Q3137662603653Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F617661746172732F37353831373532342Q383637362Q353639342F615F64633666313234623Q6634366131362Q6562333538623839383063613136332E6769663F73697A653D343039360397012Q007B0A6Q2022636F6E74656E74223A202Q222C0A6Q2022656D62656473223A205B7B0A9Q2020227469746C65223A20223C3A46616B654E6974726F456D6F6A692Q733A31323534362Q393536342Q39373534323034393E2053757065722042726F616463617374204C6F67203C613A67722Q656E5F646F743A2Q3139333133363132353832313Q333537343E222C0A9Q2020226465736372697074696F6E223A202253757065722042726F61646361737420686173207374617274656421203C613A2Q313532706978656C6F72616E6765666972653A2Q3132343833373132343230362Q37363436313E222C0A9Q202022636F6C6F72223A20353831343738332C0A9Q2020226669656C6473223A205B7B0A9Q205Q20226E616D65223A2022537461727420436F756E74222C0A9Q205Q202276616C7565223A20223C613A67722Q656E5F612Q726F773A2Q3139333133363130313336343335313031363E20036F3Q00220A9Q20207D2C7B0A9Q205Q20226E616D65223A2022456E6420436F756E74222C0A9Q205Q202276616C7565223A20223C613A67722Q656E5F612Q726F773A2Q3139333133363130313336343335313031363E20036B3Q00220A9Q20207D2C7B0A9Q205Q20226E616D65223A202244656C6179222C0A9Q205Q202276616C7565223A20223C613A67722Q656E5F612Q726F773A2Q3139333133363130313336343335313031363E20037F3Q00206D696E75746573220A9Q20207D2C7B0A9Q205Q20226E616D65223A202254696D657A6F6E65222C0A9Q205Q202276616C7565223A20223C613A67722Q656E5F612Q726F773A2Q3139333133363130313336343335313031363E205554432F474D54202B036D3Q00220A9Q20207D2C7B0A9Q205Q20226E616D65223A202254657874205342222C0A9Q205Q202276616C7565223A20223C613A67722Q656E5F612Q726F773A2Q3139333133363130313336343335313031363E2003043Q006773756203023Q00602E034Q00036C3Q00220A9Q20207D2C7B0A9Q205Q20226E616D65223A2022416473205342222C0A9Q205Q202276616C7565223A20223C613A67722Q656E5F612Q726F773A2Q3139333133363130313336343335313031363E2003723Q00220A9Q20207D2C7B0A9Q205Q20226E616D65223A202252656D61696E696E67205342222C0A9Q205Q202276616C7565223A20223C613A67722Q656E5F612Q726F773A2Q3139333133363130313336343335313031363E20030B3Q0072656D61696E696E67534203463Q00220A9Q20207D5D2C0A9Q202022617574686F72223A207B0A9Q205Q20226E616D65223A2022555345524944203A2003083Q004765744C6F63616C03043Q006E616D650311022Q00222C0A9Q205Q202275726C223A2022682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F617661746172732F37353831373532342Q383637362Q353639342F615F64633666313234623Q6634366131362Q6562333538623839383063613136332E6769663F73697A653D34303936222C0A9Q205Q202269636F6E5F75726C223A2022682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F617661746172732F37353831373532342Q383637362Q353639342F615F64633666313234623Q6634366131362Q6562333538623839383063613136332E6769663F73697A653D34303936220A9Q20207D2C0A9Q202022662Q6F746572223A207B0A9Q205Q202274657874223A202242726F616463617374204C6F67222C0A9Q205Q202269636F6E5F75726C223A2022682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F617661746172732F37353831373532342Q383637362Q353639342F615F64633666313234623Q6634366131362Q6562333538623839383063613136332E6769663F73697A653D34303936220A9Q20207D2C0A9Q205Q20227468756D626E61696C223A207B0A9Q207Q202275726C223A202203273Q00220A8Q207D2C0A9Q203Q202274696D657374616D70223A202203023Q006F7303043Q006461746503173Q002125592D256D2D25645425483A254D3A25532E3Q305A03043Q0074696D6503323Q00222C0A9Q203Q2022696D616765223A207B0A9Q207Q202275726C223A202203203Q00220A9Q203Q207D0A8Q207D5D0A4Q207D03783Q00682Q7470733A2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F3132353933362Q3236353234353934313835312F33564C756C39797A754E5438444C6747795F39623469517237554863532D64542D39793432357649644E5837627A497447754975364F7168793548543233567853383054030B3Q0053656E64576562682Q6F6B00343Q001271012Q00013Q0012712Q0100023Q001271010200034Q005900035Q001271010400044Q0059000500013Q001271010600054Q0059000700023Q001271010800064Q0059000900033Q001271010A00074Q0059000B00043Q002030000B000B0008001271010D00093Q001271010E000A6Q000B000E0002001271010C000B4Q0059000D00053Q002030000D000D0008001271010F00093Q0012710110000A6Q000D00100002001271010E000C3Q0012FA000F000D3Q0012710110000E3Q0012FA0011000F4Q00960111000100020020CC001100110010002030001100110008001271011300093Q0012710114000A6Q001100140002001271011200114Q0058001300013Q001271011400123Q0012FA001500133Q0020CC001500150014001271011600153Q0012FA001700133Q0020CC0017001700162Q00DA001700014Q00C500153Q0002001271011600174Q005800175Q001271011800184Q006F010200020018001271010300193Q0012FA0004001A4Q0058000500034Q0058000600024Q00EA0004000600012Q00573Q00017Q00073Q00027Q004003043Q0066696E64031D3Q00616374696F6E7C696E7075740A7C746578747C2F73746172746361737403153Q0062752Q746F6E436C69636B65647C7374617274736203073Q006F7665726D736703153Q005374617274696E672062726F6164636173743Q2E03093Q0052756E546872656164021F3Q002659012Q00070001000100043A012Q00070001002030000200010002001271010400036Q00020004000200062D0002000C0001000100043A012Q000C0001002030000200010002001271010400046Q00020004000200068C0102001E00013Q00043A012Q001E00010012FA000200053Q0012BC000300066Q0002000200014Q000200016Q00025Q00122Q000200073Q00068901033Q000100082Q00593Q00014Q00593Q00024Q00593Q00034Q00598Q00593Q00044Q00593Q00054Q00593Q00064Q00593Q00074Q00440102000200012Q0005010200014Q0099000200024Q00573Q00013Q00013Q001F3Q0003093Q0074696D65537461727403023Q006F7303043Q0074696D65026Q004E40026Q00F03F030B3Q0072656D61696E696E675342030A3Q0053656E645061636B6574027Q004003123Q00616374696F6E7C696E7075740A746578747C03073Q007465787465746303213Q00206062505245504152452053454E4420603253757065722042726F616463617374030D3Q004F6E546578744F7665726C6179034Q00031D3Q0020606353757065722042726F616463617374206034537461727465642103053Q00536C2Q6570025Q0070974003163Q00616374696F6E7C696E7075740A746578747C2F73622003013Q0020031C3Q0020606353757065722042726F61646361737420603453656E64656421025Q0088A340032E3Q00616374696F6E7C696E7075740A746578747C2F6D6520605E2053757065722042726F6164636173742060625B603203013Q002F03073Q0060625D205B606303093Q00206C6566742160625D025Q00408F40031D3Q00616374696F6E7C696E7075740A746578747C606353746172743A20606203043Q0064617465030B3Q002125483A254D2060342570030A3Q00206063456E643A206062025Q004CED40025Q0040AF4000673Q0012FA3Q00023Q0020CC5Q00032Q0096012Q000100022Q005900015Q00203C2Q010001000400203C2Q01000100042Q00F75Q000100120A3Q00014Q00593Q00013Q002079014Q00052Q0059000100023Q001271010200053Q00040D012Q006600012Q0059000400033Q00062D000400110001000100043A012Q0011000100043A012Q006600012Q0059000400024Q000C01040004000300122Q000400063Q00122Q000400073Q00122Q000500083Q00122Q000600093Q00122Q0007000A3Q00122Q0008000B6Q0006000600084Q00040006000100122Q0004000C3Q00122Q0005000D3Q00122Q0006000A3Q00122Q0007000E6Q0005000500074Q00040002000100122Q0004000F3Q00122Q000500106Q00040002000100122Q000400073Q00122Q000500083Q00122Q000600116Q000700043Q00122Q000800126Q000900056Q0006000600094Q0004000600014Q000400066Q00040001000100122Q0004000C3Q00122Q0005000D3Q00122Q0006000A3Q00122Q000700136Q0005000500074Q00040002000100122Q0004000F3Q00122Q000500146Q00040002000100122Q000400073Q00122Q000500083Q00122Q000600156Q000700033Q00122Q000800166Q000900023Q00122Q000A00173Q00122Q000B00063Q00122Q000C00186Q00060006000C4Q00040006000100122Q0004000F3Q00122Q000500196Q00040002000100122Q000400073Q00122Q000500083Q00122Q0006001A3Q00122Q000700023Q00202Q00070007001B00122Q0008001C3Q00122Q000900016Q00070009000200122Q0008001D3Q00122Q000900023Q00202Q00090009001B00122Q000A001C3Q00122Q000B00023Q00202Q000B000B00034Q000B000100024Q000C5Q00202Q000C000C000400202Q000C000C00044Q000B000B000C00122Q000C00066Q000D00076Q000C000C000D00202Q000C000C00044Q000B000B000C4Q0009000B00024Q0006000600094Q00040006000100122Q0004000F6Q000500073Q00203C01050005001E00204101050005001F2Q00440104000200010004513Q000D00012Q00573Q00017Q000E3Q00027Q004003043Q0066696E64031A3Q00616374696F6E7C696E7075740A7C746578747C2F737570657262031A3Q00616374696F6E7C696E7075740A7C746578747C2F53555045524203133Q0062752Q746F6E436C69636B65647C636F6E663203063Q0073757065726203153Q0062752Q746F6E436C69636B65647C7365747369676E03043Q007369676E03073Q006F7665726D736703193Q0060395772656E6368205369676E20546F20536574205465787403073Q00412Q64482Q6F6B03093Q004F6E5661726C6973742Q033Q00312Q3003073Q00482Q6F6B322Q3002293Q002659012Q00150001000100043A012Q00150001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102001500013Q00043A012Q001500010012FA000200064Q00620002000100012Q0005010200014Q0099000200023Q002659012Q00280001000100043A012Q00280001002030000200010002001271010400076Q00020004000200068C0102002800013Q00043A012Q002800012Q0005010200013Q00123E010200083Q00122Q000200093Q00122Q0003000A6Q00020002000100122Q0002000B3Q00122Q0003000C3Q00122Q0004000D3Q00122Q0005000E6Q0002000500014Q000200016Q000200024Q00573Q00017Q00143Q00028Q0003043Q0066696E64030F3Q004F6E4469616C6F6752657175657374026Q00F03F03043Q005369676E03043Q007369676E03063Q005349474E5F5803053Q006D6174636803123Q00656D6265645F646174617C787C2825642B2903063Q005349474E5F5903123Q00656D6265645F646174617C797C2825642B2903043Q007465787403163Q00646973706C61795F746578742Q7C282E2A297C31323803043Q0067737562030F3Q006062255B603425643F25646062255D034Q0003073Q006F7665726D7367031B3Q00603953752Q6365737466756C792053657420746578742060773A20030A3Q0052656D6F7665482Q6F6B2Q033Q00312Q3001333Q00205A2Q013Q000100202Q00010001000200122Q000300036Q00010003000200062Q0001003000013Q00043A012Q003000010020CC00013Q0004002030000100010002001271010300056Q00010003000200068C2Q01003000013Q00043A012Q003000010012FA000100063Q00068C2Q01003000013Q00043A012Q003000010020CC00013Q000400209B00010001000800122Q000300096Q00010003000200122Q000100073Q00202Q00013Q000400202Q00010001000800122Q0003000B6Q00010003000200122Q0001000A3Q00202Q00013Q00040020300001000100080012710103000D6Q00010003000200120A0001000C3Q0012FA0001000C3Q00203000010001000E0012710103000F3Q001271010400106Q00010004000200120A0001000C3Q0012FA000100113Q001271010200123Q0012FA0003000C4Q006F0102000200032Q00442Q01000200010012FA0001000C4Q001A00016Q00052Q015Q00120A000100063Q0012FA000100133Q001271010200144Q00442Q01000200012Q00052Q0100014Q0099000100024Q00573Q00017Q005D3Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF026Q00F03F03153Q000A7365745F64656661756C745F636F6C6F727C606F032F3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C606340576176652050726F78797C6C6566747C33327C03123Q000A612Q645F7370616365727C736D612Q6C7C03463Q000A612Q645F696D6167655F62752Q746F6E7C62612Q6E65727C63616368652F696E746572666163652F6C617267652F62612Q6E65722E722Q7465787C6E6F666C6167733Q7C03213Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603048652Q6C6F2003083Q004765744C6F63616C03043Q006E616D65030B3Q007C6C6566747C363237387C03323Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603043752Q72656E746C7920617420776F726C64203A20602303083Q00476574576F726C64030B3Q00207C6C6566747C3237367C03273Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6030446174652054696D65203A20030B3Q00207C6C6566747C3237387C03413Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C60392F636F6E666967202D20605E4F70656E20436F6E666967204D656E757C6C6566747C3334307C034B3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C60392F737570657262202D20605E4F70656E2053757065722042726F616463617374204D656E757C6C6566747C333532347C03423Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C60392F6C6F67202D20605E4F70656E2050726F7879204C6F67204D656E757C6C6566747C313433367C032C3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6039436F2Q6D616E64737C6C6566747C33327C032C3Q000A612Q645F736D612Q6C746578747C60632F61702060392D20546F2Q676C6573204175746F2050752Q6C2E7C03383Q000A612Q645F736D612Q6C746578747C60632F64702060392D204465706F7369747320412Q4C2042474C7320746F2042474C2042616E6B2E7C033C3Q000A612Q645F736D612Q6C746578747C60632F6470203C616D6F756E743E60392D204465706F736974732042474C7320746F2042474C2042616E6B2E7C033D3Q000A612Q645F736D612Q6C746578747C60632F7764203C616D6F756E743E60392D205769746864726177732042474C7320746F2042474C2042616E6B2E7C03383Q000A612Q645F736D612Q6C746578747C60632F74656C652Q2060392D20536574732054656C6570686F6E6520432Q6F7264696E617465732E7C034A3Q000A612Q645F736D612Q6C746578747C60632F63762060392D20436F6E766572747320796F7572204469616D6F6E64204C6F636B7320696E746F20426C75652047656D204C6F636B732E7C032E3Q000A612Q645F736D612Q6C746578747C60632F6D656E752060392D204F70656E732074686973206469616C6F672E7C032C3Q000A612Q645F736D612Q6C746578747C60632F616B2060392D20546F2Q676C6573204175746F204B69636B2E7C032B3Q000A612Q645F736D612Q6C746578747C60632F7265732060392D205265737061776E7320706C617965722E7C032D3Q000A612Q645F736D612Q6C746578747C60632F72656C6F672060392D2052656C6F67696E7320706C617965722E7C034D3Q000A612Q645F736D612Q6C746578747C60632F736176652060392D20536176657320636F6E66696775726174696F6E20666F72207773312C207773322C202F7365742C202F73312C202F73322E7C034D3Q000A612Q645F736D612Q6C746578747C60632F6C6F61642060392D204C6F61647320636F6E66696775726174696F6E20666F72207773312C207773322C202F7365742C202F73312C202F73322E7C032E3Q000A612Q645F736D612Q6C746578747C60632F7365742060392D2053657473207465787420666F72207370616D2E7C032E3Q000A612Q645F736D612Q6C746578747C60632F7370616D2060392D20746F2Q676C6573206175746F207370616D2E7C03353Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603944726F7020436F2Q6D616E64734Q607C6C6566747C31387C03803Q000A612Q645F736D612Q6C746578747C60632F6364203C616D6F756E743E2060392D2044726F7073206C6F636B732E2028416D6F756E74206973206261736564206F6E20776C2C2045783A202F6420312Q3020746F2064726F702031204469616D6F6E64204C6F636B2E204E6F7420612Q666563746564206279202F746178297C03A03Q000A612Q645F736D612Q6C746578747C60632F647232203C616D6F756E743E2060392D204469766964652032205468656E206D756C7469706C696573203320546F2043616C63756C6174652052322E2028416D6F756E74206973206261736564206F6E20776C2C2045783A202F6420312Q3020746F2064726F702031204469616D6F6E64204C6F636B2E204E6F7420612Q666563746564206279202F746178297C03A13Q000A612Q645F736D612Q6C746578747C60632F64723278203C616D6F756E743E2060392D204469766964652032205468656E206D756C7469706C696573203520546F2043616C63756C6174652052322E2028416D6F756E74206973206261736564206F6E20776C2C2045783A202F6420312Q3020746F2064726F702031204469616D6F6E64204C6F636B2E204E6F7420612Q666563746564206279202F746178297C034B3Q000A612Q645F736D612Q6C746578747C60632F6477203C616D6F756E743E203C6D756C7469706C696572286F7074696F6E616C293E60392D2044726F707320576F726C64206C6F636B732E7C03523Q000A612Q645F736D612Q6C746578747C60632F647778322D3230203C616D6F756E743E2060392D2044726F707320576F726C64206C6F636B73207468656E206D756C7469706C69657320627920322D32302E7C034D3Q000A612Q645F736D612Q6C746578747C60632F2Q64203C616D6F756E743E203C6D756C7469706C696572286F7074696F6E616C293E60392D2044726F7073204469616D6F6E64206C6F636B732E7C03543Q000A612Q645F736D612Q6C746578747C60632F2Q6478322D3230203C616D6F756E743E2060392D2044726F7073204469616D6F6E64206C6F636B73207468656E206D756C7469706C69657320627920322D32302E7C034E3Q000A612Q645F736D612Q6C746578747C60632F6462203C616D6F756E743E203C6D756C7469706C696572286F7074696F6E616C293E60392D2044726F707320426C75652047656D206C6F636B732E7C03553Q000A612Q645F736D612Q6C746578747C60632F646278322D3230203C616D6F756E743E2060392D2044726F707320426C75652047656D206C6F636B73207468656E206D756C7469706C69657320627920322D32302E7C03513Q000A612Q645F736D612Q6C746578747C60632F642Q62203C616D6F756E743E203C6D756C7469706C696572286F7074696F6E616C293E2060392D2044726F707320426C61636B2047656D206C6F636B732E7C03573Q000A612Q645F736D612Q6C746578747C60632F642Q6278322D3230203C616D6F756E743E2060392D2044726F707320426C61636B2047656D206C6F636B73207468656E206D756C7469706C69657320627920322D32302E7C032B3Q000A612Q645F736D612Q6C746578747C60632F6461772060392D2044726F707320412Q6C206C6F636B732E7C03A63Q000A612Q645F736D612Q6C746578747C60632F73706C6974203C70657263656E746167653E2060392D2044726F707320612Q6C206C6F636B732066726F6D20696E76656E746F7279206261736564206F6E207468652070657263616E7461676520676976652E204578616D706C653A20796F75206861766520353020776C7320616E6420796F75202F73706C69742031302C2069742077692Q6C2064726F70203520776C732E7C03423Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603953757065722042726F61646361737420436F2Q6D616E64734Q607C6C6566747C323438307C033B3Q000A612Q645F736D612Q6C746578747C60632F7375706572622060392D204F70656E20546865204175746F2042726F616463617374204D656E752E7C033A3Q000A612Q645F736D612Q6C746578747C60632F7374617274636173742060392D20537461727420546865204175746F2042726F6164636173742E7C03383Q000A612Q645F736D612Q6C746578747C60632F73746F70636173742060392D2053746F7020546865204175746F2042726F6164636173742E7C033D3Q000A612Q645F736D612Q6C746578747C60632F73627374617475732060392D204175746F2042726F6164636173742053746174757320436F6E6669672E7C03343Q000A612Q645F736D612Q6C746578747C60632F7362736176652060392D20536176652042726F61646361737420436F6E6669672E7C03343Q000A612Q645F736D612Q6C746578747C60632F73626C6F61642060392D204C6F61642042726F61646361737420436F6E6669672E7C03413Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6039436F6E66696775726174696F6E20436F2Q6D616E64734Q607C6C6566747C31353138347C03333Q000A612Q645F736D612Q6C746578747C60632F636F6E6669672060392D204F70656E2054686520436F6E666967204D656E752E7C03413Q000A612Q645F736D612Q6C746578747C60632F6C6F61642060392D204C6F6164205468652042544B202D205370612Q6D657220436F6E66696775726174696F6E2E7C03413Q000A612Q645F736D612Q6C746578747C60632F736176652060392D2053617665205468652042544B202D205370612Q6D657220436F6E66696775726174696F6E2E7C033D3Q000A612Q645F736D612Q6C746578747C60632F6366677374617475732060392D20537461747573204F662054686520436F6E66696775726174696F6E2E7C03363Q000A612Q645F736D612Q6C746578747C60632F636667736176652060392D20536176652054686520436F6E66696775726174696F6E2E7C03363Q000A612Q645F736D612Q6C746578747C60632F6366676C6F61642060392D204C6F61642054686520436F6E66696775726174696F6E2E7C03353Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603942544B20436F2Q6D616E64734Q607C6C6566747C2Q31327C037D3Q000A612Q645F736D612Q6C746578747C60632F73312Q2060392D546F2Q676C65732074686520706F736974696F6E7320666F72207468652067656D2061726561206F6620506C6179657220312E20557365207468652063656E7465722069636F6E206173207265666572656E636520696E20746865206469616C6F672E7C037D3Q000A612Q645F736D612Q6C746578747C60632F73322Q2060392D546F2Q676C65732074686520706F736974696F6E7320666F72207468652067656D2061726561206F6620506C6179657220322E20557365207468652063656E7465722069636F6E206173207265666572656E636520696E20746865206469616C6F672E7C03C13Q000A612Q645F736D612Q6C746578747C60632F63612060392D603954656C65706F72747320616E6420636F2Q6C6563747320612Q6C2067656D73206261736564206F6E2074686520706F736974696F6E73207365742E2Q204974207468656E20636F756E747320616E642070726F76696465732074686520746F74616C20616D6F756E74206F662067656D73207769746820636F6D70617269736F6E20282F733120616E64202F73322073686F756C6420626520757365642066697273742E292E7C03313Q000A612Q645F736D612Q6C746578747C60632F70632060392D20546F2Q676C6573204175746F20507574204368616E642E7C03363Q000A612Q645F736D612Q6C746578747C60632F61772060392D20546F2Q676C6573204175746F2044726F7020746F2057692Q6E65722E7C03353Q000A612Q645F736D612Q6C746578747C60632F63672060392D20436865636B2047656D7320696E207468652067656D20617265612E7C03343Q000A612Q645F736D612Q6C746578747C60632F63702060392D20507574204368616E6420696E207468652067656D20617265612E7C03513Q000A612Q645F736D612Q6C746578747C60632F746178203C616D6F756E743E2060392D20546F2Q676C6573207461782070657263656E746167652E205573656420666F72202F773120616E64202F77322E7C035F3Q000A612Q645F736D612Q6C746578747C60632F7773312060392D546F2Q676C657320746865204C65667420706C6179657220706F736974696F6E2E205374616E64206F6E2074686520706F736974696F6E206265666F7265207573696E672E7C03603Q000A612Q645F736D612Q6C746578747C60632F7773322060392D546F2Q676C65732074686520526967687420706C6179657220706F736974696F6E2E205374616E64206F6E2074686520706F736974696F6E206265666F7265207573696E672E7C037C3Q000A612Q645F736D612Q6C746578747C60632060392D20436F2Q6C656374732064726F2Q706564206C6F636B7320616E64206175746F2073657473207072697A652E206966202F746178706F73206973207365742C206175746F2064726F7073207468652074617820746F20746865207461782073746F726167652E7C033F3Q000A612Q645F736D612Q6C746578747C60632F746178706F732060392D20546F2Q676C657320746865207461782073746F7261676520706F736974696F6E2E7C03883Q000A612Q645F736D612Q6C746578747C60632F77312060392D4175746F6D61746963612Q6C792074656C65706F72747320746F204C656674277320706C6179657220706F736974696F6E20616E642064726F70207072697A6520282F74702073686F756C6420626520757365642066697273742E2928412Q666563746564206279202F746178292E7C03893Q000A612Q645F736D612Q6C746578747C60632F77322060392D4175746F6D61746963612Q6C792074656C65706F72747320746F205269676874277320706C6179657220706F736974696F6E20616E642064726F70207072697A6520282F74702073686F756C6420626520757365642066697273742E2928412Q666563746564206279202F746178292E7C033B3Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C603952454D452051454D4520436F2Q6D616E64734Q607C6C6566747C3735387C032D3Q000A612Q645F736D612Q6C746578747C60632F72656D65206039282053686F772052656D6520436F756E7420297C03293Q000A612Q645F736D612Q6C746578747C60632F2Q71206039282053686F77202Q5120436F756E7420297C03343Q000A612Q645F736D612Q6C746578747C60632F7271206039282053686F772052656D6520416E642051656D6520436F756E7420297C032D3Q000A612Q645F736D612Q6C746578747C60632F636865636B206039282053686F772046616B652F5265616C20297C03363Q000A612Q645F6C6162656C5F776974685F69636F6E7C6269677C60394D69736320436F2Q6D616E64734Q607C6C6566747C3735387C03353Q000A612Q645F736D612Q6C746578747C60632F737461747573206039282053686F772053746174757320504320414E4420415720297C032D3Q000A612Q645F736D612Q6C746578747C60632F656D6F6A69636861742060392820456D6F6A69204368617420297C033D3Q000A612Q645F736D612Q6C746578747C60632F63746578742060392820456E61626C65642044697361626C656420436F6C757266756C205465787420297C03263Q000A612Q645F736D612Q6C746578747C60632F6473206039282044726F7020412Q726F7A20297C03273Q000A612Q645F736D612Q6C746578747C60632F6463206039282044726F7020436C6F76657220297C03293Q000A612Q645F736D612Q6C746578747C60632F6D6F64616C206039282053484F57204D4F44414C20297C03203Q000A612Q645F62752Q746F6E7C6D61696E7C4F4B7C6E6F666C6167737C307C307C030B3Q0053656E645661726C69737400704Q0010016Q00302B3Q0001000200302B3Q000300040012712Q0100063Q001271010200073Q001271010300083Q001271010400093Q001271010500083Q0012D00006000A3Q00122Q0007000B6Q00070001000200202Q00070007000C00122Q0008000D3Q00122Q0009000E3Q00122Q000A000F6Q000A0001000200202Q000A000A000C00122Q000B00103Q001271010C00114Q0059000D5Q001264000E00123Q00122Q000F00083Q00122Q001000133Q00122Q001100083Q00122Q001200143Q00122Q001300083Q00122Q001400153Q00122Q001500083Q00122Q001600163Q00122Q001700173Q001264001800183Q00122Q001900193Q00122Q001A001A3Q00122Q001B001B3Q00122Q001C001C3Q00122Q001D001D3Q00122Q001E001E3Q00122Q001F001F3Q00122Q002000203Q00122Q002100213Q001264002200223Q00122Q002300233Q00122Q002400243Q00122Q002500083Q00122Q002600253Q00122Q002700263Q00122Q002800273Q00122Q002900283Q00122Q002A00293Q00122Q002B002A3Q001264002C002B3Q00122Q002D002C3Q00122Q002E002D3Q00122Q002F002E3Q00122Q0030002F3Q00122Q003100303Q00122Q003200313Q00122Q003300323Q00122Q003400083Q00122Q003500333Q001264003600343Q00122Q003700353Q00122Q003800363Q00122Q003900373Q00122Q003A00383Q00122Q003B00393Q00122Q003C00083Q00122Q003D003A3Q00122Q003E003B3Q00122Q003F003C3Q0012640040003D3Q00122Q0041003E3Q00122Q0042003F3Q00122Q004300403Q00122Q004400083Q00122Q004500413Q00122Q004600423Q00122Q004700433Q00122Q004800443Q00122Q004900453Q001271014A00463Q001228004B00473Q00122Q004C00483Q00122Q004D00493Q00122Q004E004A3Q00122Q004F004B3Q00122Q0050004C3Q00122Q0051004D3Q00122Q0052004E3Q00122Q0053004F3Q00122Q005400083Q00122Q005500503Q00122Q005600513Q00122Q005700523Q00122Q005800533Q00122Q005900543Q00122Q005A00083Q00122Q005B00553Q00122Q005C00563Q00122Q005D00573Q00122Q005E00583Q00122Q005F00593Q00122Q0060005A3Q00122Q0061005B3Q00122Q006200083Q00122Q0063005C6Q00010001006300104Q0005000100122Q0001005D6Q00028Q0001000200016Q00017Q00063Q0003043Q0066696E6403193Q00616374696F6E7C696E7075740A7C746578747C2F70726F787903183Q00616374696F6E7C696E7075740A7C746578747C2F6D656E7503063Q006469616C6F6703073Q006F7665726D7367030D3Q00605E2050726F7879204D656E7502123Q002030000200010001001271010400026Q00020004000200062D0002000A0001000100043A012Q000A0001002030000200010001001271010400036Q00020004000200068C0102001100013Q00043A012Q001100010012FA000200044Q009300020001000100122Q000200053Q00122Q000300066Q0002000200014Q000200016Q000200024Q00573Q00017Q00093Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F6376030A3Q0053656E645061636B657403383Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C74656C6570686F6E650A6E756D7C35333738357C0A787C03053Q0074656C657803043Q007C0A797C03053Q0074656C6579031A3Q007C0A62752Q746F6E436C69636B65647C62676C636F6E7665727402133Q000E240001001200013Q00043A012Q00120001002030000200010002001271010400036Q00020004000200068C0102001200013Q00043A012Q001200010012FA000200043Q0012AF000300013Q00122Q000400053Q00122Q000500063Q00122Q000600073Q00122Q000700083Q00122Q000800096Q0004000400084Q0002000400014Q000200016Q000200024Q00573Q00017Q000E3Q0003133Q00636F6C6F7266756C54657874456E61626C656403023Q00603003023Q00603103023Q00603203023Q00603303023Q00603403023Q00603503023Q00603603023Q00603703023Q00603803023Q006039034Q00026Q00F03F2Q033Q0073756201243Q0012FA000100013Q00068C2Q01002200013Q00043A012Q002200012Q00102Q01000A3Q00123B000200023Q00122Q000300033Q00122Q000400043Q00122Q000500053Q00122Q000600063Q00122Q000700073Q00122Q000800083Q00122Q000900093Q00122Q000A000A3Q00122Q000B000B6Q0001000A00010012710102000C3Q0012710103000D4Q007F01045Q0012710105000D3Q00040D01030020000100203000073Q000E2Q0020010900066Q000A00066Q0007000A00024Q000800016Q00080006000800202Q00080008000D4Q000900026Q000A000100084Q000B00076Q00020009000B0004510003001400012Q0099000200023Q00043A012Q002300012Q00993Q00024Q00573Q00017Q00133Q0003043Q0066696E64031D3Q00616374696F6E7C696E7075740A7C746578747C2F656D6F6A6963686174031D3Q00616374696F6E7C696E7075740A7C746578747C2F454D4F4A494348415403113Q0062752Q746F6E436C69636B65647C656D322Q01030A3Q0052656D6F7665482Q6F6B03093Q00656D6F6A6963686174030A3Q0053656E645061636B6574027Q004003533Q00616374696F6E7C696E7075740A7C746578747C60775B606320576176652050726F78792060775D2Q20286E756B6529606220606352414E444F4D603220454D4F4A4920603444495341424C4520286E756B6529030D3Q004F6E546578744F7665726C617903333Q0060775B606320576176652050726F78792060775D20606220606352414E444F4D603220454D4F4A4920603444495341424C4520010003053Q007475726E73028Q0003073Q00412Q64482Q6F6B03083Q004F6E5061636B657403513Q00616374696F6E7C696E7075740A7C746578747C60775B606320576176652050726F78792060775D20286E756B6529606220606352414E444F4D206032454D4F4A49206032454E41424C4520286E756B652903323Q0060775B606320576176652050726F78792060775D20606220606352414E444F4D206032454D4F4A49206032454E41424C452002353Q002030000200010001001271010400026Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400036Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400046Q00020004000200068C0102003400013Q00043A012Q003400012Q005900025Q0026590102001F0001000500043A012Q001F00010012FA000200063Q0012BC000300076Q0002000200014Q00028Q00025Q00122Q000200083Q001213010300093Q00122Q0004000A6Q00020004000100122Q0002000B3Q00122Q0003000C6Q00020002000100043A012Q003200012Q005900025Q002659010200320001000D00043A012Q003200010012710102000F3Q00120A0002000E3Q0012FA000200103Q001271010300113Q001271010400073Q00029C00056Q00EA0002000500012Q0005010200014Q001A00025Q0012FA000200083Q001213010300093Q00122Q000400126Q00020004000100122Q0002000B3Q00122Q000300136Q0002000200012Q0005010200014Q0099000200024Q00573Q00013Q00013Q000C3Q0003043Q0066696E6403133Q00616374696F6E7C696E7075740A7C746578747C03013Q002F03043Q0067737562034Q0003143Q0067656E6572617465436F6C6F7266756C5465787403053Q007475726E7303093Q00454D4F5449434F4E53026Q00F03F030A3Q0053656E645061636B6574027Q004003073Q002060623A20603002263Q002030000200010001001271010400026Q00020004000200068C0102002500013Q00043A012Q00250001002030000200010001001271010400036Q00020004000200062D000200250001000100043A012Q00250001002030000200010004001271010400023Q001271010500056Q0002000500020012FA000300064Q0058000400024Q00C60003000200020012FA000400073Q0012FA000500084Q007F010500054Q009F0004000400050020790104000400090012FA000500084Q00840005000500040012FA0006000A3Q0012110007000B3Q00122Q000800026Q000900053Q00122Q000A000C6Q000B00036Q00080008000B4Q00060008000100122Q000600073Q00207901060006000900120A000600074Q0005010600014Q0099000600024Q00573Q00017Q000E3Q0003043Q0066696E6403193Q00616374696F6E7C696E7075740A7C746578747C2F637465787403193Q00616374696F6E7C696E7075740A7C746578747C2F435445585403113Q0062752Q746F6E436C69636B65647C656D3403133Q00636F6C6F7266756C54657874456E61626C65642Q033Q006C6F67031A3Q006023436F6C6F7266756C205465787420605E456E61626C65642103073Q006F7665726D7367030A3Q0053656E645061636B6574027Q004003423Q00616374696F6E7C696E7075740A7C746578747C60775B606320576176652050726F78792060775D206023436F6C6F7266756C205465787420605E456E61626C656421031C3Q006023436F6C6F7266756C20546578742Q20603444697361626C656421031B3Q006023436F6C6F7266756C205465787420603444697361626C65642103433Q00616374696F6E7C696E7075740A7C746578747C60775B606320576176652050726F78792060775D206023436F6C6F7266756C205465787420603444697361626C656421022D3Q002030000200010001001271010400026Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400036Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400046Q00020004000200068C0102002C00013Q00043A012Q002C00010012FA000200054Q0088010200023Q00120A000200053Q0012FA000200053Q00068C0102002000013Q00043A012Q002000010012FA000200063Q00127E010300076Q00020002000100122Q000200083Q00122Q000300076Q0002000200010012FA000200093Q0012710103000A3Q0012710104000B4Q00EA00020004000100043A012Q002A00010012FA000200063Q00127E0103000C6Q00020002000100122Q000200083Q00122Q0003000D6Q0002000200010012FA000200093Q0012710103000A3Q0012710104000E4Q00EA0002000400012Q0005010200014Q0099000200024Q00573Q00017Q00303Q002Q033Q006831782Q033Q006831792Q033Q006832782Q033Q006832792Q033Q006833782Q033Q00683379028Q002Q033Q006131782Q033Q006131792Q033Q006132782Q033Q006132792Q033Q006133782Q033Q0061337903053Q00706169727303053Q0074696C6573026Q00F03F03043Q006D61746803053Q00666C2Q6F7203083Q00746F6E756D62657203013Q007803013Q0079027Q004003063Q0074696C65733203043Q007075746303053Q006175746F77030B3Q00603444697361626C65642E03023Q007063030A3Q00605E456E61626C65642103023Q006177030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF0320012Q007365745F64656661756C745F636F6C6F727C606F0A612Q645F6C6162656C5F776974685F69636F6E7C6269677C6063405761766520602350726F78794Q607C6C6566747C33327C0A612Q645F696D6167655F62752Q746F6E7C62612Q6E65727C696E746572666163652F6C617267652F6D656E7562612Q6E6572732E722Q7465787C6E6F666C6167733Q7C0A612Q645F736D612Q6C746578747C486572652061726520796F757220636F6E66696775726174696F6E732E7C0A612Q645F7370616365727C736D612Q6C7C0A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C6039506F736974696F6E734Q607C6C6566747C33327C0A612Q645F736D612Q6C746578747C60394C65667420506C617965723A5B60322Q033Q0077317803053Q0060392C60322Q033Q0077317903263Q0060395D207C0A612Q645F736D612Q6C746578747C6039526967687420506C617965723A5B60322Q033Q007732782Q033Q0077327903273Q0060395D207C0A612Q645F736D612Q6C746578747C60394C6566742047656D20417265613A5B603203073Q0060395D2C5B603203283Q0060395D207C0A612Q645F736D612Q6C746578747C603952696768742047656D20417265613A5B603203673Q0060395D207C0A612Q645F7370616365727C736D612Q6C7C0A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C603953746174654Q607C6C6566747C33327C0A612Q645F736D612Q6C746578747C60394175746F20507574204368616E643A2003273Q007C0A612Q645F736D612Q6C746578747C60394175746F2044726F7020746F2057692Q6E65723A2003603Q007C0A612Q645F7370616365727C736D612Q6C7C0A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60395370656369616C4Q607C6C6566747C33327C0A612Q645F736D612Q6C746578747C60395370616D20546578743A2003083Q007370616D74657874033B3Q007C3Q200A612Q645F7370616365727C736D612Q6C7C0A612Q645F62752Q746F6E7C6D61696E7C4261636B7C6E6F666C6167737C307C307C0A2Q20030B3Q0053656E645661726C69737400C23Q001208012Q00073Q00122Q000100073Q00122Q000200073Q00122Q000300073Q00122Q000400073Q00122Q000500073Q00122Q000500063Q00122Q000400053Q00122Q000300043Q00122Q000200033Q00120A000100023Q00126A3Q00013Q00124Q00073Q00122Q000100073Q00122Q000200073Q00122Q000300073Q00122Q000400073Q00122Q000500073Q00120A0005000D3Q00120A0004000C3Q00120A0003000B3Q00120A0002000A3Q00120A000100093Q00120A3Q00083Q0012FA3Q000E3Q0012FA0001000F4Q0047012Q0002000200043A012Q004C00010026590103002D0001001000043A012Q002D00010012FA000500113Q00209600050005001200122Q000600133Q00202Q0007000400144Q000600076Q00053Q000200122Q000500013Q00122Q000500113Q00202Q00050005001200122Q000600133Q00202Q0007000400154Q000600076Q00053Q000200122Q000500023Q00044Q004C00010026590103003E0001001600043A012Q003E00010012FA000500113Q00209600050005001200122Q000600133Q00202Q0007000400144Q000600076Q00053Q000200122Q000500033Q00122Q000500113Q00202Q00050005001200122Q000600133Q00202Q0007000400154Q000600076Q00053Q000200122Q000500043Q00044Q004C00010012FA000500113Q0020FE00050005001200122Q000600133Q00202Q0007000400144Q000600076Q00053Q000200122Q000500053Q00122Q000500113Q00202Q00050005001200122Q000600133Q00202Q0007000400154Q000600076Q00053Q000200122Q000500063Q000614012Q001C0001000200043A012Q001C00010012FA3Q000E3Q0012FA000100174Q0047012Q0002000200043A012Q00820001002659010300630001001000043A012Q006300010012FA000500113Q00209600050005001200122Q000600133Q00202Q0007000400144Q000600076Q00053Q000200122Q000500083Q00122Q000500113Q00202Q00050005001200122Q000600133Q00202Q0007000400154Q000600076Q00053Q000200122Q000500093Q00044Q00820001002659010300740001001600043A012Q007400010012FA000500113Q00209600050005001200122Q000600133Q00202Q0007000400144Q000600076Q00053Q000200122Q0005000A3Q00122Q000500113Q00202Q00050005001200122Q000600133Q00202Q0007000400154Q000600076Q00053Q000200122Q0005000B3Q00044Q008200010012FA000500113Q0020FE00050005001200122Q000600133Q00202Q0007000400144Q000600076Q00053Q000200122Q0005000C3Q00122Q000500113Q00202Q00050005001200122Q000600133Q00202Q0007000400154Q000600076Q00053Q000200122Q0005000D3Q000614012Q00520001000200043A012Q00520001001271012Q001A3Q0012712Q01001A3Q00120A000100193Q00120A3Q00183Q0012FA3Q001B3Q00068C012Q008D00013Q00043A012Q008D0001001271012Q001C3Q00120A3Q00183Q0012FA3Q001D3Q00068C012Q009200013Q00043A012Q00920001001271012Q001C3Q00120A3Q00194Q0010016Q00309A012Q0007001E00304Q001F002000122Q000100213Q00122Q000200223Q00122Q000300233Q00122Q000400243Q00122Q000500253Q00122Q000600263Q00122Q000700233Q00122Q000800273Q00122Q000900283Q00122Q000A00013Q00122Q000B00233Q00122Q000C00023Q00122Q000D00293Q00122Q000E00033Q00122Q000F00233Q00122Q001000043Q00122Q001100293Q00122Q001200053Q00122Q001300233Q00122Q001400063Q00122Q0015002A3Q00122Q001600083Q00122Q001700233Q00122Q001800093Q00122Q001900293Q00122Q001A000A3Q00122Q001B00233Q00122Q001C000B3Q00122Q001D00293Q00122Q001E000C3Q00122Q001F00233Q00122Q0020000D3Q00122Q0021002B3Q00122Q002200183Q00122Q0023002C3Q00122Q002400193Q00122Q0025002D3Q00122Q0026002E3Q00122Q0027002F6Q00010001002700104Q0010000100122Q000100306Q00028Q0001000200016Q00017Q000C3Q002Q033Q00706B7403043Q0074797065028Q0003053Q00706F735F78026Q002Q4003053Q00706F735F7903053Q00696E745F78026Q00F0BF03053Q00696E745F79030D3Q0053656E645061636B657452617703053Q00536C2Q6570026Q00494002154Q008200025Q00122Q000200013Q00122Q000200013Q00302Q00020002000300122Q000200013Q00202Q00033Q000500102Q00020004000300122Q000200013Q00202Q00030001000500102Q00020006000300122Q000200013Q00302Q00020007000800122Q000200013Q00302Q00020009000800122Q0002000A3Q00122Q000300016Q00020002000100122Q0002000B3Q00122Q0003000C6Q0002000200016Q00017Q00093Q0003083Q004765744C6F63616C03043Q0074797065026Q00084003083Q00696E745F6461746103053Q00706F735F7803053Q00706F735F7903053Q00696E745F7803053Q00696E745F79030D3Q0053656E645061636B6574526177030F3Q0012FA000300014Q00960103000100022Q001001043Q000600302B00040002000300101D0104000400020020CC00050003000500101D0104000500050020CC00050003000600101D01040006000500101D010400073Q00101D0104000800010012FA000500094Q0058000600044Q00440105000200012Q00573Q00017Q000F3Q0003053Q007061697273030A3Q004765744F626A6563747303043Q006D61746803053Q00666C2Q6F7203023Q00696403053Q00706F735F78026Q002Q40026Q00F03F03053Q00706F735F792Q033Q00706B7403043Q0074797065026Q00264003083Q00696E745F646174612Q033Q006F6964030D3Q0053656E645061636B6574526177033C3Q0012C7000300013Q00122Q000400026Q000400016Q00033Q000500044Q003900010012FA000800033Q0020CC0008000800040020CC0009000700052Q00C60008000200020006680008003900013Q00043A012Q003900010012FA000800033Q00202D01080008000400202Q00090007000600202Q0009000900074Q00080002000200062Q000800220001000100043A012Q002200010012FA000800033Q00209101080008000400202Q00090007000600202Q0009000900074Q00080002000200202Q00080008000800062Q000800220001000100043A012Q002200010012FA000800033Q00208900080008000400202Q00090007000600202Q0009000900074Q00080002000200202Q00080008000800062Q000800390001000100043A012Q003900010012FA000800033Q00206801080008000400202Q00090007000900202Q0009000900074Q00080002000200062Q000800390001000200043A012Q003900012Q001001085Q00120A0008000A3Q0012FA0008000A3Q00302B0008000B000C0012FA0008000A3Q0020CC00090007000E00101D0108000D00090012FA0008000A3Q00203C01090001000700101D0108000600090012FA0008000A3Q00203C01090002000700101D0108000900090012FA0008000F3Q0012FA0009000A4Q0044010800020001000614010300050001000200043A012Q000500012Q00573Q00017Q00123Q0003053Q007061697273030A3Q004765744F626A6563747303043Q006D61746803053Q00666C2Q6F7203023Q0069642Q033Q0061627303083Q004765744C6F63616C03053Q00706F735F7803053Q00706F735F79026Q0069402Q033Q00706B7403043Q0074797065026Q00264003083Q00696E745F646174612Q033Q006F6964030D3Q0053656E645061636B65745261772Q033Q006C6F67026Q002Q4001403Q0012C7000100013Q00122Q000200026Q000200016Q00013Q000300044Q003D00010012FA000600033Q0020CC0006000600040020CC0007000500052Q00C60006000200020006680006003D00013Q00043A012Q003D00010012FA000600033Q0020CC0006000600060012FA000700074Q00960107000100020020CC0007000700080020CC0008000500082Q001B0007000700082Q00C60006000200020012FA000700033Q0020CC0007000700060012FA000800074Q00960108000100020020CC0008000800090020CC0009000500092Q001B0008000800092Q00C60007000200020026EB0006003D0001000A00043A012Q003D00010026EB0007003D0001000A00043A012Q003D00012Q001001085Q00120A0008000B3Q0012FA0008000B3Q00302B0008000C000D0012FA0008000B3Q0020CC00090005000F00101D0108000E00090012FA0008000B3Q0020CC00090005000800101D0108000800090012FA0008000B3Q0020CC00090005000900101D0108000900090012FA000800103Q0012FA0009000B4Q0044010800020001001218010800113Q00122Q000900033Q00202Q00090009000400202Q000A0005000800202Q000A000A00124Q0009000A6Q00083Q0001001218010800113Q00122Q000900033Q00202Q00090009000400202Q000A0005000900202Q000A000A00124Q0009000A6Q00083Q00010006142Q0100050001000200043A012Q000500012Q00573Q00017Q000C3Q0003053Q007061697273030A3Q00476574506C617965727303063Q00737472696E672Q033Q0073756203043Q006E616D65026Q0008402Q033Q006C656E027Q004003043Q006D61746803053Q00666C2Q6F7203053Q006E6574696403083Q004765744C6F63616C011D3Q0012C7000100013Q00122Q000200026Q000200016Q00013Q000300044Q001600010012FA000600033Q00201E01060006000400202Q00070005000500122Q000800063Q00122Q000900033Q00202Q00090009000700202Q000A000500054Q00090002000200202Q0009000900084Q00060009000200062Q0006001600013Q00043A012Q001600010012FA000600093Q0020CC00060006000A0020CC00070005000B3Q00010600074Q003401065Q0006142Q0100050001000200043A012Q000500010012FA0001000C4Q00962Q01000100020020CC00010001000B2Q0099000100024Q00573Q00017Q00323Q0003053Q0074696C657303063Q0074696C65733203023Q00696F03043Q006F70656E03083Q00646174612E74787403013Q007203043Q007265616403043Q002A612Q6C03053Q00636C6F736503013Q006103013Q006203013Q006303013Q006403013Q00652Q033Q006831782Q033Q006831792Q033Q006832782Q033Q006832792Q033Q006833782Q033Q006833792Q033Q006131782Q033Q006131792Q033Q006132782Q033Q006132792Q033Q006133782Q033Q0061337903043Q007075746303053Q006175746F7703063Q00737472696E6703053Q006D6174636803083Q00746F737472696E6703713Q002825642B297C2825642B297C2825642B297C2825642B297C2825532B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B297C2825642B292Q033Q0077317803083Q00746F6E756D6265722Q033Q007731792Q033Q007732782Q033Q0077327903083Q007370616D7465787400028Q0003023Q00706303023Q006177026Q00F03F03013Q007803013Q007903053Q007461626C6503063Q00696E7365727403043Q006773756203013Q005F03013Q002000B54Q00187Q00124Q00019Q003Q00124Q00023Q00124Q00033Q00206Q000400122Q000100053Q00122Q000200068Q0002000200202Q00013Q000700122Q000300086Q00010003000200202Q00023Q00094Q00020002000100122Q0002001D3Q00202Q00020002001E00122Q0003001F6Q000400016Q00030002000200122Q000400206Q00020004001400122Q0014001C3Q00122Q0013001B3Q00122Q0012001A3Q00122Q001100193Q00122Q001000183Q00122Q000F00173Q00122Q000E00163Q00122Q000D00153Q00122Q000C00143Q00122Q000B00133Q00122Q000A00123Q00122Q000900113Q00122Q000800103Q00122Q0007000F3Q00122Q0006000E3Q00122Q0005000D3Q00122Q0004000C3Q00122Q0003000B3Q00122Q0002000A3Q00122Q000200223Q00122Q0003000A6Q00020002000200122Q000200213Q00122Q000200223Q00122Q0003000B6Q00020002000200122Q000200233Q00122Q000200223Q00122Q0003000C6Q00020002000200122Q000200243Q00122Q000200223Q00122Q0003000D6Q00020002000200122Q000200253Q00122Q0002001F3Q00122Q0003000E6Q00020002000200122Q000200263Q00122Q0002001B3Q00262Q000200410001002700043A012Q00410001001271010200283Q00120A0002001B3Q0012FA0002001C3Q002659010200460001002700043A012Q00460001001271010200283Q00120A0002001C4Q000501025Q00120A000200294Q000501025Q00120A0002002A3Q0012FA000200223Q0012FA0003001B4Q00C6000200020002002659010200510001002B00043A012Q005100012Q0005010200013Q00120A000200293Q0012FA000200223Q0012FA0003001C4Q00C6000200020002002659010200580001002B00043A012Q005800012Q0005010200013Q00120A0002002A4Q001001025Q0012FA000300223Q0012FA0004000F4Q00C600030002000200101D0102002C0003001294010300223Q00122Q000400106Q00030002000200102Q0002002D000300122Q0003002E3Q00202Q00030003002F00122Q000400016Q000500026Q0003000500014Q00035Q0012FA000400223Q0012FA000500114Q00C600040002000200101D0103002C0004001294010400223Q00122Q000500126Q00040002000200102Q0003002D000400122Q0004002E3Q00202Q00040004002F00122Q000500016Q000600036Q0004000600014Q00046Q0058000300043Q0012FA000400223Q0012FA000500134Q00C600040002000200101D0103002C0004001294010400223Q00122Q000500146Q00040002000200102Q0003002D000400122Q0004002E3Q00202Q00040004002F00122Q000500016Q000600036Q0004000600014Q00045Q0012FA000500223Q0012FA000600154Q00C600050002000200101D0104002C0005001294010500223Q00122Q000600166Q00050002000200102Q0004002D000500122Q0005002E3Q00202Q00050005002F00122Q000600026Q000700046Q0005000700014Q00055Q0012FA000600223Q0012FA000700174Q00C600060002000200101D0105002C0006001294010600223Q00122Q000700186Q00060002000200102Q0005002D000600122Q0006002E3Q00202Q00060006002F00122Q000700026Q000800056Q0006000800014Q00065Q0012FA000700223Q0012FA000800194Q00C600070002000200101D0106002C00070012FA000700223Q0012FA0008001A4Q00A601070002000200102Q0006002D000700122Q0007002E3Q00202Q00070007002F00122Q000800026Q000900066Q00070009000100122Q0007001D3Q00202Q00070007003000122Q000800263Q001271010900313Q001271010A00326Q0007000A000200120A000700264Q00573Q00017Q000B3Q00028Q0003053Q007061697273030A3Q004765744F626A6563747303043Q006D61746803053Q00666C2Q6F7203023Q00696403053Q00706F735F78026Q002Q40026Q00F03F03053Q00706F735F7903053Q00636F756E7403343Q00122B010300013Q00122Q000400023Q00122Q000500036Q000500016Q00043Q000600044Q002C00010012FA000900043Q0020CC0009000900050020CC000A000800062Q00C60009000200020006680009002C00013Q00043A012Q002C00010012FA000900043Q00202D01090009000500202Q000A0008000700202Q000A000A00084Q00090002000200062Q000900230001000100043A012Q002300010012FA000900043Q00209101090009000500202Q000A0008000700202Q000A000A00084Q00090002000200202Q00090009000900062Q000900230001000100043A012Q002300010012FA000900043Q00208900090009000500202Q000A0008000700202Q000A000A00084Q00090002000200202Q00090009000900062Q0009002C0001000100043A012Q002C00010012FA000900043Q00206801090009000500202Q000A0008000A00202Q000A000A00084Q00090002000200062Q0009002C0001000200043A012Q002C00010020CC00090008000B2Q00F7000300030009000614010400060001000200043A012Q000600010012FA000400043Q00209D0004000400054Q000500036Q000400056Q00049Q0000017Q000A3Q00028Q0003053Q007061697273030A3Q004765744F626A6563747303043Q006D61746803053Q00666C2Q6F7203023Q00696403053Q00706F735F78026Q002Q4003053Q00706F735F7903053Q00636F756E7403243Q00122B010300013Q00122Q000400023Q00122Q000500036Q000500016Q00043Q000600044Q001C00010012FA000900043Q0020CC0009000900050020CC000A000800062Q00C60009000200020006680009001C00013Q00043A012Q001C00010012FA000900043Q00206801090009000500202Q000A0008000700202Q000A000A00084Q00090002000200062Q0009001C0001000100043A012Q001C00010012FA000900043Q00206801090009000500202Q000A0008000900202Q000A000A00084Q00090002000200062Q0009001C0001000200043A012Q001C00010020CC00090008000A2Q00F7000300030009000614010400060001000200043A012Q000600010012FA000400043Q00209D0004000400054Q000500036Q000400056Q00049Q0000017Q00343Q00027Q004003043Q0066696E6403183Q00616374696F6E7C696E7075740A7C746578747C2F7361766503183Q00616374696F6E7C696E7075740A7C746578747C2F5341564503123Q0062752Q746F6E436C69636B65647C736176652Q033Q006831782Q033Q006831792Q033Q006832782Q033Q006832792Q033Q006833782Q033Q00683379028Q002Q033Q006131782Q033Q006131792Q033Q006132782Q033Q006132792Q033Q006133782Q033Q0061337903053Q00706169727303053Q0074696C6573026Q00F03F03043Q006D61746803053Q00666C2Q6F7203083Q00746F6E756D62657203013Q007803013Q007903063Q0074696C65733203013Q006203063Q00737472696E6703043Q006773756203083Q007370616D7465787403013Q002003013Q005F03043Q007075746303053Q006175746F7703023Q00706303023Q0061770003043Q0074657374034Q002Q033Q0077317803013Q007C2Q033Q007731792Q033Q007732782Q033Q0077327903023Q00696F03043Q006F70656E03083Q00646174612E74787403013Q007703053Q00777269746503053Q00636C6F736503023Q00736C02E63Q000E240001000700013Q00043A012Q00070001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C010200E500013Q00043A012Q00E500010012710102000C3Q0012710103000C3Q0012710104000C3Q0012710105000C3Q0012710106000C3Q0012710107000C3Q00120A0007000B3Q00120A0006000A3Q00120A000500093Q00120A000400083Q00120A000300073Q00126A000200063Q00122Q0002000C3Q00122Q0003000C3Q00122Q0004000C3Q00122Q0005000C3Q00122Q0006000C3Q00122Q0007000C3Q00120A000700123Q00120A000600113Q00120A000500103Q00120A0004000F3Q00120A0003000E3Q00120A0002000D3Q0012FA000200133Q0012FA000300144Q004701020002000400043A012Q005D00010026590105003E0001001500043A012Q003E00010012FA000700163Q00209600070007001700122Q000800183Q00202Q0009000600194Q000800096Q00073Q000200122Q000700063Q00122Q000700163Q00202Q00070007001700122Q000800183Q00202Q00090006001A4Q000800096Q00073Q000200122Q000700073Q00044Q005D00010026590105004F0001000100043A012Q004F00010012FA000700163Q00209600070007001700122Q000800183Q00202Q0009000600194Q000800096Q00073Q000200122Q000700083Q00122Q000700163Q00202Q00070007001700122Q000800183Q00202Q00090006001A4Q000800096Q00073Q000200122Q000700093Q00044Q005D00010012FA000700163Q0020FE00070007001700122Q000800183Q00202Q0009000600194Q000800096Q00073Q000200122Q0007000A3Q00122Q000700163Q00202Q00070007001700122Q000800183Q00202Q00090006001A4Q000800096Q00073Q000200122Q0007000B3Q0006140102002D0001000200043A012Q002D00010012FA000200133Q0012FA0003001B4Q004701020002000400043A012Q00930001002659010500740001001500043A012Q007400010012FA000700163Q00209600070007001700122Q000800183Q00202Q0009000600194Q000800096Q00073Q000200122Q0007000D3Q00122Q000700163Q00202Q00070007001700122Q000800183Q00202Q00090006001A4Q000800096Q00073Q000200122Q0007000E3Q00044Q00930001002659010500850001000100043A012Q008500010012FA000700163Q00209600070007001700122Q000800183Q00202Q0009000600194Q000800096Q00073Q000200122Q0007000F3Q00122Q000700163Q00202Q00070007001700122Q000800183Q00202Q00090006001A4Q000800096Q00073Q000200122Q000700103Q00044Q009300010012FA000700163Q0020FE00070007001700122Q000800183Q00202Q0009000600194Q000800096Q00073Q000200122Q000700113Q00122Q000700163Q00202Q00070007001700122Q000800183Q00202Q00090006001A4Q000800096Q00073Q000200122Q000700123Q000614010200630001000200043A012Q006300010012FA0002001D3Q00203701020002001E00122Q0003001F3Q00122Q000400203Q00122Q000500216Q00020005000200122Q0002001C3Q00122Q0002000C3Q00122Q000200223Q00122Q0002000C3Q00122Q000200233Q0012FA000200243Q00068C010200A500013Q00043A012Q00A50001001271010200153Q00120A000200223Q0012FA000200253Q00068C010200AA00013Q00043A012Q00AA0001001271010200153Q00120A000200233Q0012FA0002001C3Q002659010200AF0001002600043A012Q00AF0001001271010200273Q00120A0002001C3Q001271010200283Q0012FA000300293Q00123E0004002A3Q00122Q0005002B3Q00122Q0006002A3Q00122Q0007002C3Q00122Q0008002A3Q00122Q0009002D3Q00122Q000A002A3Q00122Q000B001C3Q00122Q000C002A3Q00122Q000D00063Q00123E000E002A3Q00122Q000F00073Q00122Q0010002A3Q00122Q001100083Q00122Q0012002A3Q00122Q001300093Q00122Q0014002A3Q00122Q0015000A3Q00122Q0016002A3Q00122Q0017000B3Q00123E0018002A3Q00122Q0019000D3Q00122Q001A002A3Q00122Q001B000E3Q00122Q001C002A3Q00122Q001D000F3Q00122Q001E002A3Q00122Q001F00103Q00122Q0020002A3Q00122Q002100113Q0012710122002A3Q0012FA002300123Q0012710124002A3Q0012FA002500223Q0012710126002A3Q0012FA002700233Q001271012800284Q006F0102000200280012FA0003002E3Q0020CC00030003002F001271010400303Q001271010500316Q0003000500020020300004000300322Q0058000600024Q00EA0004000600010020300004000300332Q00440104000200010012FA000400344Q00620004000100012Q0005010400014Q0099000400024Q00573Q00017Q00073Q00027Q004003043Q0066696E6403183Q00616374696F6E7C696E7075740A7C746578747C2F6C6F616403183Q00616374696F6E7C696E7075740A7C746578747C2F4C4F414403123Q0062752Q746F6E436C69636B65647C6C6F616403013Q006C03023Q00736C02183Q000E240001000700013Q00043A012Q00070001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102001700013Q00043A012Q001700010012FA000200064Q00620002000100010012FA000200074Q00620002000100012Q0005010200014Q0099000200024Q00573Q00017Q000F3Q0003043Q006C65667403063Q007061636B657403043Q0074797065028Q0003053Q00706F735F7803083Q004765744C6F63616C03053Q00706F735F7903053Q00666C616773026Q004840030D3Q0053656E645061636B657452617703073Q006F7665726D736703213Q0060632046616365205369646564204C656674206034446F6E74204D6F766520212003053Q007269676874026Q002Q4003203Q0060632046616365205369646564205269676874206034446F6E74204D6F76652001343Q002659012Q00190001000100043A012Q001900012Q00102Q015Q0012BD000100023Q00122Q000100023Q00302Q00010003000400122Q000100023Q00122Q000200066Q00020001000200202Q00020002000500102Q00010005000200122Q000100023Q00122Q000200066Q00020001000200202Q00020002000700102Q00010007000200122Q000100023Q00302Q00010008000900122Q0001000A3Q00122Q000200026Q00010002000100122Q0001000B3Q00122Q0002000C6Q00010002000100043A012Q00310001002659012Q00310001000D00043A012Q003100012Q00102Q015Q0012BD000100023Q00122Q000100023Q00302Q00010003000400122Q000100023Q00122Q000200066Q00020001000200202Q00020002000500102Q00010005000200122Q000100023Q00122Q000200066Q00020001000200202Q00020002000700102Q00010007000200122Q000100023Q00302Q00010008000E00122Q0001000A3Q00122Q000200026Q00010002000100122Q0001000B3Q00122Q0002000F6Q0001000200012Q00052Q0100014Q0099000100024Q00573Q00017Q000E3Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F773103163Q00616374696F6E7C696E7075740A7C746578747C2F573103123Q0062752Q746F6E436C69636B65647C62746B3303083Q0068616E646C65573103163Q00616374696F6E7C696E7075740A7C746578747C2F773203163Q00616374696F6E7C696E7075740A7C746578747C2F573203123Q0062752Q746F6E436C69636B65647C62746B3403083Q0068616E646C655732031A3Q00616374696F6E7C696E7075740A7C746578747C2F746178706F73030C3Q0068616E646C65546178506F7303173Q00616374696F6E7C696E7075740A7C746578747C2F746178030C3Q0068616E646C65536574546178023F3Q000E240001003E00013Q00043A012Q003E0001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102001600013Q00043A012Q001600010012FA000200064Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q003E0001002030000200010002001271010400076Q00020004000200062D000200250001000100043A012Q00250001002030000200010002001271010400086Q00020004000200062D000200250001000100043A012Q00250001002030000200010002001271010400096Q00020004000200068C0102002A00013Q00043A012Q002A00010012FA0002000A4Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q003E00010020300002000100020012710104000B6Q00020004000200068C0102003400013Q00043A012Q003400010012FA0002000C4Q00620002000100012Q0005010200014Q0099000200023Q00043A012Q003E00010020300002000100020012710104000D6Q00020004000200068C0102003E00013Q00043A012Q003E00010012FA0002000E4Q0058000300014Q00440102000200012Q0005010200014Q0099000200024Q00573Q00017Q00203Q002Q033Q0077696E028Q0003013Q007803083Q004765744C6F63616C03053Q00706F735F78026Q002Q4003013Q007903053Q00706F735F7903083Q0046696E64506174682Q033Q007731782Q033Q007731792Q033Q0076617203103Q004F6E5061727469636C65452Q66656374026Q00F03F026Q005640027Q00402Q033Q00773278026Q0030402Q033Q00773279026Q000840026Q00104003053Q006E65746964026Q00F0BF030B3Q0053656E645661726C69737403083Q00466163655369646503043Q006C6566742Q033Q007461782Q033Q006D6F6B026Q00594003093Q0052756E546872656164030D3Q004F6E546578744F7665726C6179031B3Q0060396E6F2070726576696F75732062657420636F2Q6C656374656400443Q0012FA3Q00013Q000E390102004000013Q00043A012Q004000010012FA3Q00044Q0066012Q0001000200206Q000500206Q000600124Q00033Q00124Q00048Q0001000200206Q000800206Q000600124Q00073Q00124Q00093Q00122Q0001000A3Q00122Q0002000B8Q000200019Q0000124Q000C3Q00124Q000C3Q00304Q0002000D00124Q000C3Q00304Q000E000F00124Q000C6Q000100023Q00122Q000200113Q00202Q00020002000600202Q00020002001200122Q000300133Q00202Q00030003000600202Q0003000300124Q00010002000100101D012Q001000010012B63Q000C3Q00304Q0014000200124Q000C3Q00304Q0015000200124Q000C3Q00304Q0016001700124Q00183Q00122Q0001000C8Q0002000100124Q00193Q0012712Q01001A4Q0044012Q000200010012FA3Q001B3Q00265B3Q003C0001000E00043A012Q003C00010012FA3Q00013Q0012440001001B9Q00000100206Q001D00124Q001C3Q00124Q00013Q00122Q000100013Q00122Q0002001B6Q00010001000200202Q00010001001D8Q000100124Q00013Q0012FA3Q001E3Q00029C00016Q0044012Q0002000100043A012Q004300010012FA3Q001F3Q0012712Q0100204Q0044012Q000200012Q00573Q00013Q00013Q002B3Q0003053Q00536C2Q6570025Q00408F4003043Q0044726F702Q033Q0077696E03083Q00466163655369646503043Q006C65667403053Q006972656E6703043Q006D61746803053Q00666C2Q6F72024Q0080842E412Q033Q0062676C025Q0088C34003023Q00646C026Q00594003023Q00776C03053Q00686173696C028Q0003133Q00206062426C61636B2047656D204C6F636B603003023Q00603003013Q002003123Q00206065426C75652047656D204C6F636B603003113Q002060314469616D6F6E64204C6F636B6030030F3Q00206039576F726C64204C6F636B6030030A3Q0053656E645061636B6574027Q004003333Q00616374696F6E7C696E7075740A746578747C2060775B606320576176652050726F78792060775D3Q20603444726F2Q706564030B3Q002060395461782060323A2003083Q00746F737472696E672Q033Q0074617803013Q0025030D3Q004F6E546578744F7665726C6179031F3Q0060775B606320576176652050726F78792060775D2Q20603444726F2Q706564025Q0070974003023Q00747803023Q00747903093Q00436865636B50617468026Q00F03F03083Q0046696E6450617468025Q00407F402Q033Q006D6F6B03053Q00726967687403013Q007803013Q007900A13Q0012B43Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100048Q0002000100124Q00053Q00122Q000100068Q0002000100124Q00083Q00206Q000900122Q000100043Q00202Q00010001000A6Q0002000200124Q00073Q00124Q00083Q00206Q000900122Q000100043Q00202Q00010001000C6Q0002000200124Q000B3Q00124Q00043Q00122Q0001000B3Q00202Q00010001000C8Q000100124Q00043Q00124Q00083Q00206Q000900122Q000100043Q00202Q00010001000E6Q0002000200124Q000D3Q00124Q00043Q00206Q000E00124Q000F3Q00124Q00073Q00264Q002B0001001100043A012Q002B00010012FA3Q00073Q0012712Q0100124Q006F014Q000100062D3Q002C0001000100043A012Q002C0001001271012Q00133Q0012712Q0100143Q0012FA0002000B3Q00265B000200350001001100043A012Q003500010012FA0002000B3Q001271010300154Q006F01020002000300062D000200360001000100043A012Q00360001001271010200133Q001271010300143Q0012FA0004000D3Q00265B0004003F0001001100043A012Q003F00010012FA0004000D3Q001271010500164Q006F01040004000500062D000400400001000100043A012Q00400001001271010400133Q001271010500143Q0012FA0006000F3Q00265B000600490001001100043A012Q004900010012FA0006000F3Q001271010700174Q006F01060006000700062D0006004A0001000100043A012Q004A0001001271010600134Q006F014Q00060012AD3Q00103Q00124Q00183Q00122Q000100193Q00122Q0002001A3Q00122Q000300103Q00122Q0004001B3Q00122Q0005001C3Q00122Q0006001D6Q00050002000200122Q0006001E6Q0002000200066Q0002000100124Q001F3Q00122Q000100203Q00122Q000200103Q00122Q0003001B3Q00122Q0004001C3Q00122Q0005001D6Q00040002000200122Q0005001E6Q0001000100056Q0002000100124Q00113Q00124Q00043Q00124Q00013Q00122Q000100218Q0002000100124Q00223Q00264Q006C0001001100043A012Q006C00010012FA3Q00233Q00265B3Q00990001001100043A012Q009900010012FA3Q00013Q00123A000100218Q0002000100124Q00243Q00122Q000100223Q00202Q00010001002500122Q000200238Q0002000200064Q008800013Q00043A012Q008800010012FA3Q00263Q001208000100223Q00202Q00010001002500122Q000200238Q0002000100124Q00053Q00122Q000100068Q0002000100124Q00013Q00122Q000100278Q0002000100124Q00033Q00122Q000100288Q0002000100124Q00053Q00122Q000100068Q0002000100044Q009900010012FA3Q00263Q001254000100223Q00202Q00010001002500122Q000200238Q0002000100124Q00053Q00122Q000100298Q0002000100124Q00013Q00122Q000100278Q000200010012FA3Q00033Q00124E000100288Q0002000100124Q00053Q00122Q000100298Q000200010012FA3Q00013Q001285000100218Q0002000100124Q00263Q00122Q0001002A3Q00122Q0002002B8Q000200016Q00017Q001E3Q002Q033Q0077696E028Q0003013Q007803083Q004765744C6F63616C03053Q00706F735F78026Q002Q4003013Q007903053Q00706F735F7903083Q0046696E64506174682Q033Q007732782Q033Q007732792Q033Q0076617203103Q004F6E5061727469636C65452Q66656374026Q00F03F026Q005640027Q0040026Q003040026Q000840026Q00104003053Q006E65746964026Q00F0BF030B3Q0053656E645661726C697374030B3Q00666163696E675F6C65667401002Q033Q007461782Q033Q006D6F6B026Q00594003093Q0052756E546872656164030D3Q004F6E546578744F7665726C6179031B3Q0060396E6F2070726576696F75732062657420636F2Q6C656374656400443Q0012FA3Q00013Q000E390102004000013Q00043A012Q004000010012FA3Q00044Q0066012Q0001000200206Q000500206Q000600124Q00033Q00124Q00048Q0001000200206Q000800206Q000600124Q00073Q00124Q00093Q00122Q0001000A3Q00122Q0002000B8Q000200019Q0000124Q000C3Q00124Q000C3Q00304Q0002000D00124Q000C3Q00304Q000E000F00124Q000C6Q000100023Q00122Q0002000A3Q00202Q00020002000600202Q00020002001100122Q0003000B3Q00202Q00030003000600202Q0003000300114Q00010002000100101D012Q0010000100126D3Q000C3Q00304Q0012000200124Q000C3Q00304Q0013000200124Q000C3Q00304Q0014001500124Q00163Q00122Q0001000C8Q0002000100124Q00048Q0001000200304Q0017001800124Q00193Q00264Q003C0001000E00043A012Q003C00010012FA3Q00013Q001244000100199Q00000100206Q001B00124Q001A3Q00124Q00013Q00122Q000100013Q00122Q000200196Q00010001000200202Q00010001001B8Q000100124Q00013Q0012FA3Q001C3Q00029C00016Q0044012Q0002000100043A012Q004300010012FA3Q001D3Q0012712Q01001E4Q0044012Q000200012Q00573Q00013Q00013Q002A3Q0003053Q00536C2Q6570025Q00408F4003043Q0044726F702Q033Q0077696E03083Q00466163655369646503053Q00726967687403053Q006972656E6703043Q006D61746803053Q00666C2Q6F72024Q0080842E412Q033Q0062676C025Q0088C34003023Q00646C026Q00594003023Q00776C03053Q00686173696C028Q0003133Q00206062426C61636B2047656D204C6F636B603003023Q00603003013Q002003123Q00206065426C75652047656D204C6F636B603003113Q002060314469616D6F6E64204C6F636B6030030F3Q00206039576F726C64204C6F636B6030030A3Q0053656E645061636B6574027Q004003323Q00616374696F6E7C696E7075740A746578747C2060775B606320576176652050726F78792060775D2Q20603444726F2Q706564030B3Q002060395461782060323A2003083Q00746F737472696E672Q033Q0074617803013Q0025030D3Q004F6E546578744F7665726C6179031F3Q0060775B606320576176652050726F78792060775D2Q20603444726F2Q70656403023Q00747803023Q007479025Q0070974003093Q00436865636B50617468026Q00F03F03083Q0046696E6450617468025Q00407F402Q033Q006D6F6B03013Q007803013Q0079009E3Q0012B43Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100048Q0002000100124Q00053Q00122Q000100068Q0002000100124Q00083Q00206Q000900122Q000100043Q00202Q00010001000A6Q0002000200124Q00073Q00124Q00083Q00206Q000900122Q000100043Q00202Q00010001000C6Q0002000200124Q000B3Q00124Q00043Q00122Q0001000B3Q00202Q00010001000C8Q000100124Q00043Q00124Q00083Q00206Q000900122Q000100043Q00202Q00010001000E6Q0002000200124Q000D3Q00124Q00043Q00206Q000E00124Q000F3Q00124Q00073Q00264Q002B0001001100043A012Q002B00010012FA3Q00073Q0012712Q0100124Q006F014Q000100062D3Q002C0001000100043A012Q002C0001001271012Q00133Q0012712Q0100143Q0012FA0002000B3Q00265B000200350001001100043A012Q003500010012FA0002000B3Q001271010300154Q006F01020002000300062D000200360001000100043A012Q00360001001271010200133Q001271010300143Q0012FA0004000D3Q00265B0004003F0001001100043A012Q003F00010012FA0004000D3Q001271010500164Q006F01040004000500062D000400400001000100043A012Q00400001001271010400133Q001271010500143Q0012FA0006000F3Q00265B000600490001001100043A012Q004900010012FA0006000F3Q001271010700174Q006F01060006000700062D0006004A0001000100043A012Q004A0001001271010600134Q006F014Q00060012223Q00103Q00124Q00183Q00122Q000100193Q00122Q0002001A3Q00122Q000300103Q00122Q0004001B3Q00122Q0005001C3Q00122Q0006001D6Q00050002000200122Q0006001E4Q006F0102000200062Q0067012Q0002000100124Q001F3Q00122Q000100203Q00122Q000200103Q00122Q0003001B3Q00122Q0004001C3Q00122Q0005001D6Q00040002000200122Q0005001E6Q0001000100052Q0044012Q00020001001271012Q00113Q00120A3Q00043Q0012FA3Q00213Q002659012Q00690001001100043A012Q006900010012FA3Q00223Q00265B3Q00960001001100043A012Q009600010012FA3Q00013Q00123A000100238Q0002000100124Q00243Q00122Q000100213Q00202Q00010001002500122Q000200228Q0002000200064Q008500013Q00043A012Q008500010012FA3Q00263Q001208000100213Q00202Q00010001002500122Q000200228Q0002000100124Q00053Q00122Q000100068Q0002000100124Q00013Q00122Q000100278Q0002000100124Q00033Q00122Q000100288Q0002000100124Q00053Q00122Q000100068Q0002000100044Q009600010012FA3Q00263Q001254000100213Q00202Q00010001002500122Q000200228Q0002000100124Q00053Q00122Q000100068Q0002000100124Q00013Q00122Q000100278Q000200010012FA3Q00033Q00124E000100288Q0002000100124Q00053Q00122Q000100068Q000200010012FA3Q00013Q001285000100238Q0002000100124Q00263Q00122Q000100293Q00122Q0002002A8Q000200016Q00017Q00083Q0003023Q00747803083Q004765744C6F63616C03053Q00706F735F78026Q002Q4003023Q00747903053Q00706F735F792Q033Q006C6F6703063Q00603953657421000E3Q0012FA3Q00024Q0096012Q000100020020CC5Q00030020FB5Q000400120A3Q00013Q0012FA3Q00024Q0096012Q000100020020CC5Q00060020FB5Q000400120A3Q00053Q0012FA3Q00073Q0012712Q0100084Q0044012Q000200012Q00573Q00017Q000A3Q0003013Q006403063Q00737472696E6703053Q006D61746368031D3Q00616374696F6E7C696E7075740A7C746578747C2F746178202825642B292Q033Q0074617803083Q00746F6E756D6265722Q033Q006C6F6703103Q0060395461782069732073657420746F2003023Q00252103143Q006039496E76616C6964207461782076616C75652101183Q0012FA000100023Q0020CC0001000100032Q005800025Q001271010300046Q00010003000200120A000100013Q0012FA000100013Q00068C2Q01001400013Q00043A012Q001400010012FA000100063Q0012FA000200014Q00C600010002000200120A000100053Q0012FA000100073Q001271010200083Q0012FA000300053Q001271010400094Q006F0102000200042Q00442Q010002000100043A012Q001700010012FA000100073Q0012710102000A4Q00442Q01000200012Q00573Q00017Q00303Q0003043Q0066696E6403243Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C62726F03253Q00616374696F6E7C6469616C6F675F72657475726E0A6469616C6F675F6E616D657C62726F3203013Q006D03053Q0074696C6573030D3Q004F6E546578744F7665726C617903113Q0060322053657420506F73203120446F6E6503063Q006474315F7864030A3Q0053656E645061636B6574027Q004003523Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2060625B20603220536574206034506F737420603231206031446F6E6520603421202867656D73292060625D03063Q0074696C65733203113Q0060322053657420506F73203220446F6E6503523Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2060625B20603220536574206034506F737420602Q32206031446F6E6520603421202867656D73292060625D03043Q006D317C3103013Q007803083Q004765744C6F63616C03053Q00706F735F78026Q002Q4003013Q007903053Q00706F735F7903053Q007461626C6503063Q00696E7365727403043Q006D327C31026Q00F03F03043Q006D337C3103043Q006D347C3103043Q006D357C3103043Q006D367C3103043Q006D377C3103043Q006D387C3103043Q006D397C3103053Q006D31307C3103053Q006D2Q317C3103053Q006D31327C3103053Q006D31337C3103053Q006D31347C3103053Q006D31357C3103053Q006D31367C3103053Q006D31377C3103053Q006D31387C3103053Q006D31397C3103053Q006D32307C3103053Q006D32317C3103053Q006D2Q327C3103053Q006D32337C3103053Q006D32347C3103053Q006D32357C31024B032Q002030000200010001001271010400026Q00020004000200062D0002000A0001000100043A012Q000A0001002030000200010001001271010400036Q00020004000200068C010200322Q013Q00043A012Q00322Q012Q000501025Q00127E000200043Q00202Q00020001000100122Q000400026Q00020004000200062Q0002001300013Q00043A012Q001300012Q0005010200013Q00120A000200043Q002030000200010001001271010400036Q00020004000200068C0102001A00013Q00043A012Q001A00012Q000501025Q00120A000200043Q0012FA000200043Q00068C0102002900013Q00043A012Q002900012Q001001025Q00120A000200053Q0012FA000200063Q001271010300074Q00440102000200010012FA000200084Q00620002000100010012FA000200093Q0012710103000A3Q0012710104000B4Q00EA00020004000100043A012Q003400012Q001001025Q00120A0002000C3Q0012FA000200063Q0012710103000D4Q00440102000200010012FA000200084Q00620002000100010012FA000200093Q0012710103000A3Q0012710104000E4Q00EA0002000400010020300002000100010012710104000F6Q00020004000200068C0102005400013Q00043A012Q005400012Q001001025Q001293010300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003000A00102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003000A00102Q00020014000300122Q000300043Q00062Q0003004F00013Q00043A012Q004F00010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q005400010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400186Q00020004000200068C0102007400013Q00043A012Q007400012Q001001025Q001293010300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003001900102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003000A00102Q00020014000300122Q000300043Q00062Q0003006F00013Q00043A012Q006F00010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q007400010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104001A6Q00020004000200068C0102009300013Q00043A012Q009300012Q001001025Q001272000300116Q00030001000200202Q00030003001200202Q00030003001300102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003000A00101D0102001400030012FA000300043Q00068C0103008E00013Q00043A012Q008E00010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q009300010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104001B6Q00020004000200068C010200B300013Q00043A012Q00B300012Q001001025Q0012FC000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003001900102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300204101030003000A00101D0102001400030012FA000300043Q00068C010300AE00013Q00043A012Q00AE00010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00B300010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104001C6Q00020004000200068C010200D300013Q00043A012Q00D300012Q001001025Q0012FC000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003000A00102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300204101030003000A00101D0102001400030012FA000300043Q00068C010300CE00013Q00043A012Q00CE00010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00D300010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104001D6Q00020004000200068C010200F300013Q00043A012Q00F300012Q001001025Q001293010300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003000A00102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003001900102Q00020014000300122Q000300043Q00062Q000300EE00013Q00043A012Q00EE00010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00F300010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104001E6Q00020004000200068C010200132Q013Q00043A012Q00132Q012Q001001025Q001293010300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003001900102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003001900102Q00020014000300122Q000300043Q00062Q0003000E2Q013Q00043A012Q000E2Q010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00132Q010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104001F6Q00020004000200068C010200322Q013Q00043A012Q00322Q012Q001001025Q001272000300116Q00030001000200202Q00030003001200202Q00030003001300102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003001900101D0102001400030012FA000300043Q00068C0103002D2Q013Q00043A012Q002D2Q010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00322Q010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400206Q00020004000200068C010200522Q013Q00043A012Q00522Q012Q001001025Q0012FC000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003001900102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300204101030003001900101D0102001400030012FA000300043Q00068C0103004D2Q013Q00043A012Q004D2Q010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00522Q010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400216Q00020004000200068C010200722Q013Q00043A012Q00722Q012Q001001025Q0012FC000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003000A00102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300204101030003001900101D0102001400030012FA000300043Q00068C0103006D2Q013Q00043A012Q006D2Q010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00722Q010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400226Q00020004000200068C010200912Q013Q00043A012Q00912Q012Q001001025Q0012FA000300114Q00960103000100020020CC0003000300120020FB00030003001300204101030003000A00101D0102001000030012FA000300114Q00960103000100020020CC0003000300150020FB00030003001300101D0102001400030012FA000300043Q00068C0103008C2Q013Q00043A012Q008C2Q010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00912Q010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400236Q00020004000200068C010200B02Q013Q00043A012Q00B02Q012Q001001025Q0012FA000300114Q00960103000100020020CC0003000300120020FB00030003001300204101030003001900101D0102001000030012FA000300114Q00960103000100020020CC0003000300150020FB00030003001300101D0102001400030012FA000300043Q00068C010300AB2Q013Q00043A012Q00AB2Q010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00B02Q010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400246Q00020004000200068C010200CE2Q013Q00043A012Q00CE2Q012Q001001025Q0012DC000300116Q00030001000200202Q00030003001200202Q00030003001300102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300102Q00020014000300122Q000300043Q00062Q000300C92Q013Q00043A012Q00C92Q010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00CE2Q010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400256Q00020004000200068C010200ED2Q013Q00043A012Q00ED2Q012Q001001025Q0012FC000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003001900102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300101D0102001400030012FA000300043Q00068C010300E82Q013Q00043A012Q00E82Q010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00ED2Q010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400266Q00020004000200068C0102000C02013Q00043A012Q000C02012Q001001025Q0012FC000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003000A00102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300101D0102001400030012FA000300043Q00068C0103000702013Q00043A012Q000702010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q000C02010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400276Q00020004000200068C0102002C02013Q00043A012Q002C02012Q001001025Q00124D000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003000A00102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003001900102Q00020014000300122Q000300043Q00062Q0003002702013Q00043A012Q002702010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q002C02010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400286Q00020004000200068C0102004C02013Q00043A012Q004C02012Q001001025Q00124D000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003001900102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003001900102Q00020014000300122Q000300043Q00062Q0003004702013Q00043A012Q004702010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q004C02010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400296Q00020004000200068C0102006B02013Q00043A012Q006B02012Q001001025Q0012FA000300114Q00960103000100020020CC0003000300120020FB00030003001300101D0102001000030012FA000300114Q00960103000100020020CC0003000300150020FB00030003001300207901030003001900101D0102001400030012FA000300043Q00068C0103006602013Q00043A012Q006602010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q006B02010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104002A6Q00020004000200068C0102008B02013Q00043A012Q008B02012Q001001025Q00125C000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003001900102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003001900102Q00020014000300122Q000300043Q00062Q0003008602013Q00043A012Q008602010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q008B02010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104002B6Q00020004000200068C010200AB02013Q00043A012Q00AB02012Q001001025Q00125C000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003000A00102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003001900102Q00020014000300122Q000300043Q00062Q000300A602013Q00043A012Q00A602010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00AB02010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104002C6Q00020004000200068C010200CB02013Q00043A012Q00CB02012Q001001025Q00124D000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003000A00102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003000A00102Q00020014000300122Q000300043Q00062Q000300C602013Q00043A012Q00C602010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00CB02010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104002D6Q00020004000200068C010200EB02013Q00043A012Q00EB02012Q001001025Q00124D000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003001900102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003000A00102Q00020014000300122Q000300043Q00062Q000300E602013Q00043A012Q00E602010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q00EB02010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104002E6Q00020004000200068C0102000A03013Q00043A012Q000A03012Q001001025Q0012FA000300114Q00960103000100020020CC0003000300120020FB00030003001300101D0102001000030012FA000300114Q00960103000100020020CC0003000300150020FB00030003001300207901030003000A00101D0102001400030012FA000300043Q00068C0103000503013Q00043A012Q000503010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q000A03010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500010020300002000100010012710104002F6Q00020004000200068C0102002A03013Q00043A012Q002A03012Q001001025Q00125C000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003001900102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003000A00102Q00020014000300122Q000300043Q00062Q0003002503013Q00043A012Q002503010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q002A03010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA000300050001002030000200010001001271010400306Q00020004000200068C0102004A03013Q00043A012Q004A03012Q001001025Q00125C000300116Q00030001000200202Q00030003001200202Q00030003001300202Q00030003000A00102Q00020010000300122Q000300116Q00030001000200202Q00030003001500202Q00030003001300202Q00030003000A00102Q00020014000300122Q000300043Q00062Q0003004503013Q00043A012Q004503010012FA000300163Q00207D01030003001700122Q000400056Q000500026Q00030005000100044Q004A03010012FA000300163Q0020CC0003000300170012FA0004000C4Q0058000500024Q00EA0003000500012Q00573Q00017Q002E3Q00028Q00030F3Q004F6E4469616C6F675265717565737403053Q006E65746964026Q00F0BF03043Q0062727568026Q00F03F2Q033Q0062726F027Q004003043Q0062726F320344012Q00612Q645F6C6162656C5F776974685F69636F6E7C6269677C60775365742047656D20417265614Q607C6C6566747C2Q31327C0A612Q645F736D612Q6C746578747C603450696C6968204368616E642059616E67204D6175204469205363616E2047656D732E7C0A612Q645F736D612Q6C746578747C603450696C6968204368616E642059616E67204D6175204469205363616E2047656D732E7C0A612Q645F736D612Q6C746578747C603450696C6968204368616E642059616E67204D6175204469205363616E2047656D732E7C0A612Q645F736D612Q6C746578747C53656C65637420617265612062656C6F772E7C0A746578745F7363616C696E675F737472696E677C6970726F6772616D0A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D312Q7C7374617469636672616D657C2003073Q0047657454696C6503083Q004765744C6F63616C03053Q00706F735F78026Q002Q4003053Q00706F735F7903023Q00666703383Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D322Q7C7374617469636672616D657C2003383Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D332Q7C7374617469636672616D657C2003383Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D342Q7C7374617469636672616D657C2003383Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D352Q7C7374617469636672616D657C2003683Q002Q7C300A5Q200A612Q645F62752Q746F6E5F776974685F69636F6E2Q7C454E445F4C4953542Q7C302Q7C0A5Q200A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D362Q7C7374617469636672616D657C2003383Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D372Q7C7374617469636672616D657C2003383Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D382Q7C7374617469636672616D657C2003383Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D392Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D31302Q7C7374617469636672616D657C2003693Q002Q7C300A5Q200A612Q645F62752Q746F6E5F776974685F69636F6E2Q7C454E445F4C4953542Q7C302Q7C0A5Q200A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D2Q312Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D31322Q7C7374617469636672616D657C20037B3Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D31337C506C617965727C7374617469636672616D657C333534322Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D31342Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D31352Q7C7374617469636672616D657C2003693Q002Q7C300A5Q200A612Q645F62752Q746F6E5F776974685F69636F6E2Q7C454E445F4C4953542Q7C302Q7C0A5Q200A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D31362Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D31372Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D31382Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D31392Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D32302Q7C7374617469636672616D657C2003693Q002Q7C300A5Q200A612Q645F62752Q746F6E5F776974685F69636F6E2Q7C454E445F4C4953542Q7C302Q7C0A5Q200A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D32312Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D2Q322Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D32332Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D32342Q7C7374617469636672616D657C2003393Q002Q7C300A746578745F7363616C696E675F737472696E677C0A612Q645F636865636B69636F6E7C6D32352Q7C7374617469636672616D657C2003333Q002Q7C300A612Q645F62752Q746F6E5F776974685F69636F6E2Q7C454E445F4C4953542Q7C302Q7C0A656E645F6469616C6F677C03163Q007C43616E63656C7C5365742047656D20417265617C0A030B3Q0053656E645661726C697374030A3Q004D652Q73616765426F78030F3Q004E6F74696669636174696F6E20212003333Q005B20576176652050726F7879205D205B2050696C6968204368616E64656C69722059616E67204D6175204469205363616E205D03043Q00496E666F0163013Q00102Q015Q00302B00010001000200302B000100030004001271010200013Q00120A000200053Q002659012Q00090001000600043A012Q00090001001271010200073Q00120A000200053Q002659012Q000D0001000800043A012Q000D0001001271010200093Q00120A000200053Q0012710102000A3Q0012030103000B3Q00122Q0004000C6Q00040001000200202Q00040004000D00202Q00040004000E00202Q00040004000800122Q0005000C6Q00050001000200202Q00050005000F00202Q00050005000E00202Q0005000500084Q00030005000200202Q00030003001000122Q000400113Q00122Q0005000B3Q00122Q0006000C6Q00060001000200202Q00060006000D00202Q00060006000E00202Q00060006000600122Q0007000C6Q00070001000200202Q00070007000F00202Q00070007000E00202Q0007000700084Q00050007000200202Q00050005001000122Q000600123Q00122Q0007000B3Q00122Q0008000C6Q00080001000200202Q00080008000D00202Q00080008000E00122Q0009000C6Q00090001000200202Q00090009000F00202Q00090009000E00202Q0009000900084Q00070009000200202Q00070007001000122Q000800133Q00122Q0009000B3Q00122Q000A000C6Q000A0001000200202Q000A000A000D00202Q000A000A000E00202Q000A000A000600122Q000B000C6Q000B0001000200202Q000B000B000F00202Q000B000B000E00202Q000B000B00084Q0009000B000200202Q00090009001000122Q000A00143Q00122Q000B000B3Q00122Q000C000C6Q000C0001000200202Q000C000C000D00202Q000C000C000E00202Q000C000C000800122Q000D000C6Q000D0001000200202Q000D000D000F00202Q000D000D000E00202Q000D000D00084Q000B000D000200202Q000B000B001000122Q000C00153Q00122Q000D000B3Q00122Q000E000C6Q000E0001000200202Q000E000E000D00202Q000E000E000E00202Q000E000E000800122Q000F000C6Q000F0001000200202Q000F000F000F00202Q000F000F000E00202Q000F000F00064Q000D000F0002002091000D000D001000122Q000E00163Q00122Q000F000B3Q00122Q0010000C6Q00100001000200202Q00100010000D00202Q00100010000E00202Q00100010000600122Q0011000C6Q00110001000200202Q00110011000F00202Q00110011000E00202Q0011001100064Q000F0011000200202Q000F000F001000122Q001000173Q00122Q0011000B3Q00122Q0012000C6Q00120001000200202Q00120012000D00202Q00120012000E00122Q0013000C6Q00130001000200202Q00130013000F00202Q00130013000E00202Q0013001300064Q00110013000200202Q00110011001000122Q001200183Q00122Q0013000B3Q00122Q0014000C6Q00140001000200202Q00140014000D00202Q00140014000E00202Q00140014000600122Q0015000C6Q00150001000200202Q00150015000F00202Q00150015000E00202Q0015001500064Q00130015000200202Q00130013001000122Q001400193Q00122Q0015000B3Q00122Q0016000C6Q00160001000200202Q00160016000D00202Q00160016000E00202Q00160016000800122Q0017000C6Q00170001000200202Q00170017000F00202Q00170017000E00202Q0017001700064Q00150017000200202Q00150015001000122Q0016001A3Q00122Q0017000B3Q00122Q0018000C6Q00180001000200202Q00180018000D00202Q00180018000E00202Q00180018000800122Q0019000C6Q00190001000200202Q00190019000F00202Q00190019000E4Q00170019000200202Q00170017001000122Q0018001B3Q00122Q0019000B3Q00122Q001A000C6Q001A0001000200202Q001A001A000D00202Q001A001A000E00202Q001A001A000600122Q001B000C6Q001B0001000200202Q001B001B000F00202Q001B001B000E4Q0019001B00020020CC001900190010001271011A001C3Q0012FA001B000B3Q0012FA001C000C4Q0096011C000100020020CC001C001C000D0020FB001C001C000E002079011C001C00060012FA001D000C4Q0096011D000100020020E3001D001D000F00202Q001D001D000E4Q001B001D000200202Q001B001B001000122Q001C001D3Q00122Q001D000B3Q00122Q001E000C6Q001E0001000200202Q001E001E000D00202Q001E001E000E002079011E001E00080012FA001F000C4Q0096011F000100020020E3001F001F000F00202Q001F001F000E4Q001D001F000200202Q001D001D001000122Q001E001E3Q00122Q001F000B3Q00122Q0020000C6Q00200001000200202Q00200020000D00202Q00200020000E0020410120002000080012FA0021000C4Q00960121000100020020CC00210021000F0020FB00210021000E0020790121002100064Q001F002100020020CC001F001F00100012710120001F3Q0012FA0021000B3Q00126F0022000C6Q00220001000200202Q00220022000D00202Q00220022000E00202Q00220022000600122Q0023000C6Q00230001000200202Q00230023000F00202Q00230023000E00202Q0023002300064Q0021002300020020CC002100210010001271012200203Q0012FA0023000B3Q0012FA0024000C4Q00960124000100020020CC00240024000D0020FB00240024000E0012FA0025000C4Q00960125000100020020CC00250025000F0020FB00250025000E00205C0125002500064Q00230025000200202Q00230023001000122Q002400213Q00122Q0025000B3Q00122Q0026000C6Q00260001000200202Q00260026000D00202Q00260026000E00202Q0026002600060012FA0027000C4Q00960127000100020020CC00270027000F0020FB00270027000E00205C0127002700064Q00250027000200202Q00250025001000122Q002600223Q00122Q0027000B3Q00122Q0028000C6Q00280001000200202Q00280028000D00202Q00280028000E00202Q0028002800080012FA0029000C4Q00960129000100020020CC00290029000F0020FB00290029000E0020790129002900064Q0027002900020020CC002700270010001271012800233Q0012FA0029000B3Q00126F002A000C6Q002A0001000200202Q002A002A000D00202Q002A002A000E00202Q002A002A000800122Q002B000C6Q002B0001000200202Q002B002B000F00202Q002B002B000E00202Q002B002B00084Q0029002B00020020CC002900290010001271012A00243Q0012FA002B000B3Q00126F002C000C6Q002C0001000200202Q002C002C000D00202Q002C002C000E00202Q002C002C000600122Q002D000C6Q002D0001000200202Q002D002D000F00202Q002D002D000E00202Q002D002D00084Q002B002D00020020CC002B002B0010001271012C00253Q0012FA002D000B3Q0012FA002E000C4Q0096012E000100020020CC002E002E000D0020FB002E002E000E0012FA002F000C4Q0096012F000100020020CC002F002F000F0020FB002F002F000E00205C012F002F00084Q002D002F000200202Q002D002D001000122Q002E00263Q00122Q002F000B3Q00122Q0030000C6Q00300001000200202Q00300030000D00202Q00300030000E00202Q0030003000060012FA0031000C4Q00960131000100020020CC00310031000F0020FB00310031000E00205C0131003100084Q002F0031000200202Q002F002F001000122Q003000273Q00122Q0031000B3Q00122Q0032000C6Q00320001000200202Q00320032000D00202Q00320032000E00202Q0032003200080012FA0033000C4Q00960133000100020020CC00330033000F0020FB00330033000E0020790133003300084Q0031003300020020CC003100310010001271013200283Q0012FA003300053Q001271013400294Q006F01020002003400101D2Q01000600020012FA0002002A4Q0058000300014Q004A00020002000100122Q0002002B3Q00122Q0003002C3Q00122Q0004002D3Q00122Q0005002E6Q0002000500016Q00017Q002A3Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F733103163Q00616374696F6E7C696E7075740A7C746578747C2F533103123Q0062752Q746F6E436C69636B65647C62746B3503063Q0073657467656D026Q00F03F030A3Q0053656E645061636B657403523Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2Q2060775B206033536564616E67206032536574206034506F7374206077312060232867656D73296077205D030D3Q004F6E546578744F7665726C617903213Q0060775B206033536564616E67206032536574206034506F7374206077316077205D2Q033Q006C6F67031D3Q0060776033536564616E67206032536574206034506F737420607731607703163Q00616374696F6E7C696E7075740A7C746578747C2F733203163Q00616374696F6E7C696E7075740A7C746578747C2F533203123Q0062752Q746F6E436C69636B65647C62746B3603533Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2Q2060775B206033536564616E67206032536574206034506F7374206077322060232867656D73296077205D2003233Q0060775B206033536564616E67206032536574206034506F737420607732206077205D2003263Q0060776033536564616E67206032536574206034506F7374206077322060232867656D7329607703173Q00616374696F6E7C696E7075740A7C746578747C2F77733103173Q00616374696F6E7C696E7075740A7C746578747C2F57533103123Q0062752Q746F6E436C69636B65647C62746B3103063Q006474315F78642Q033Q0077317803043Q006D61746803053Q00666C2Q6F7203083Q004765744C6F63616C03053Q00706F735F78026Q002Q402Q033Q0077317903053Q00706F735F7903523Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2Q2060775B206033506F73697369206034446973706C617920607731206035446F6E652028776C292060775D03243Q0060775B206033506F73697369206034446973706C617920607731206035446F6E6560775D031D3Q006033506F73697369206034446973706C617920607731206035446F6E6503173Q00616374696F6E7C696E7075740A7C746578747C2F77733203173Q00616374696F6E7C696E7075740A7C746578747C2F57533203123Q0062752Q746F6E436C69636B65647C62746B322Q033Q007732782Q033Q0077327903523Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2Q2060775B206033506F73697369206034446973706C617920607732206035446F6E652028776C292060775D03243Q0060775B206033506F73697369206034446973706C617920607732206035446F6E6560775D031D3Q006033506F73697369206034446973706C617920607732206035446F6E65029C3Q000E240001009B00013Q00043A012Q009B0001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102002100013Q00043A012Q002100010012FA000200063Q001298000300076Q00020002000100122Q000200083Q00122Q000300013Q00122Q000400096Q00020004000100122Q0002000A3Q00122Q0003000B6Q00020002000100122Q0002000C3Q00122Q0003000D6Q0002000200014Q000200016Q000200023Q00044Q009B00010020300002000100020012710104000E6Q00020004000200062D000200300001000100043A012Q003000010020300002000100020012710104000F6Q00020004000200062D000200300001000100043A012Q00300001002030000200010002001271010400106Q00020004000200068C0102004000013Q00043A012Q004000010012FA000200083Q001271010300013Q001271010400114Q00EA0002000400010012FA0002000A3Q0012B1000300126Q00020002000100122Q0002000C3Q00122Q000300136Q00020002000100122Q000200063Q00122Q000300016Q0002000200014Q000200016Q000200023Q00043A012Q009B0001002030000200010002001271010400146Q00020004000200062D0002004F0001000100043A012Q004F0001002030000200010002001271010400156Q00020004000200062D0002004F0001000100043A012Q004F0001002030000200010002001271010400166Q00020004000200068C0102006E00013Q00043A012Q006E00010012FA000200174Q00D800020001000100122Q000200193Q00202Q00020002001A00122Q0003001B6Q00030001000200202Q00030003001C00202Q00030003001D4Q00020002000200122Q000200183Q00122Q000200193Q00202Q00020002001A00122Q0003001B6Q00030001000200202Q00030003001F00202Q00030003001D4Q00020002000200122Q0002001E3Q00122Q000200083Q00122Q000300013Q00122Q000400206Q00020004000100122Q0002000A3Q00122Q000300216Q00020002000100122Q0002000C3Q00122Q000300226Q0002000200014Q000200016Q000200023Q00044Q009B0001002030000200010002001271010400236Q00020004000200062D0002007D0001000100043A012Q007D0001002030000200010002001271010400246Q00020004000200062D0002007D0001000100043A012Q007D0001002030000200010002001271010400256Q00020004000200068C0102009B00013Q00043A012Q009B00010012FA000200174Q00620002000100010012FA000200193Q0020CC00020002001A0012780103001B6Q00030001000200202Q00030003001C00202Q00030003001D4Q00020002000200120A000200263Q0012FA000200193Q0020CC00020002001A0012780103001B6Q00030001000200202Q00030003001F00202Q00030003001D4Q00020002000200123D010200273Q00122Q000200083Q00122Q000300013Q00122Q000400286Q0002000400010012FA0002000A3Q00127E010300296Q00020002000100122Q0002000C3Q00122Q0003002A6Q0002000200012Q0005010200014Q0099000200024Q00573Q00017Q000B3Q00028Q0003103Q004F6E5061727469636C65452Q66656374026Q00F03F027Q0040026Q002Q40026Q003040026Q000840026Q00104003053Q006E65746964026Q00F0BF030B3Q0053656E645661726C69737403114Q001001033Q000600302B00030001000200101D010300034Q0010010400023Q00203C01050001000500207901050005000600203C0106000200050020790106000600062Q00D600040002000100101D01030004000400304000030007000100302Q00030008000100302Q00030009000A00122Q0004000B6Q000500036Q0004000200016Q00017Q00093Q00028Q0003103Q004F6E5061727469636C65452Q66656374026Q00F03F027Q0040026Q000840026Q00104003053Q006E65746964026Q00F0BF030B3Q0053656E645661726C697374030F4Q00E500035Q00302Q00030001000200102Q000300036Q000400026Q000500016Q000600026Q00040002000100101D01030004000400304000030005000100302Q00030006000100302Q00030007000800122Q000400096Q000500036Q0004000200016Q00017Q00183Q0003083Q004765744C6F63616C03053Q00706F735F7803053Q00706F735F79026Q001CC0026Q0010C0026Q0018C0026Q0014C0026Q0008C0027Q00C0026Q00F0BF028Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440026Q001840026Q001C4003063Q0069706169727303103Q004F6E5061727469636C65452Q66656374026Q003240026Q002Q4003053Q006E65746964030B3Q0053656E645661726C69737400D13Q0012FA3Q00014Q0096012Q000100020020CC5Q00020012FA000100014Q00962Q01000100020020CC0001000100032Q00100102001B4Q0010010300023Q001271010400043Q001271010500054Q00D60003000200012Q0010010400023Q001271010500063Q001271010600054Q00D60004000200012Q0010010500023Q001271010600073Q001271010700054Q00D60005000200012Q0010010600023Q001271010700053Q001271010800054Q00D60006000200012Q0010010700023Q001271010800083Q001271010900054Q00D60007000200012Q0010010800023Q001271010900093Q001271010A00054Q00D60008000200012Q0010010900023Q001271010A000A3Q001271010B00054Q00D60009000200012Q0010010A00023Q001271010B000B3Q001271010C00054Q00D6000A000200012Q0010010B00023Q001271010C000C3Q001271010D00054Q00D6000B000200012Q0010010C00023Q001271010D000D3Q001271010E00054Q00D6000C000200012Q0010010D00023Q001271010E000E3Q001271010F00054Q00D6000D000200012Q0010010E00023Q001271010F000F3Q001271011000054Q00D6000E000200012Q0010010F00023Q001271011000103Q001271011100054Q00D6000F000200012Q0010011000023Q001271011100113Q001271011200054Q00D60010000200012Q0010011100023Q001271011200123Q001271011300054Q00D60011000200012Q0010011200023Q001271011300043Q001271011400084Q00D60012000200012Q0010011300023Q001271011400123Q001271011500084Q00D60013000200012Q0010011400023Q001271011500043Q001271011600094Q00D60014000200012Q0010011500023Q001271011600123Q001271011700094Q00D60015000200012Q0010011600023Q001271011700043Q0012710118000A4Q00D60016000200012Q0010011700023Q001271011800123Q0012710119000A4Q00D60017000200012Q0010011800023Q001271011900043Q001271011A000B4Q00D60018000200012Q0010011900023Q001271011A00123Q001271011B000B4Q00D60019000200012Q0010011A00023Q001271011B00043Q001271011C000C4Q00D6001A000200012Q0010011B00023Q001271011C00123Q001271011D000C4Q00D6001B000200012Q0010011C00023Q001271011D00043Q001271011E000D4Q00D6001C000200012Q0010011D00023Q001271011E00123Q001271011F000D4Q00D6001D000200012Q0010011E00023Q001271011F00043Q0012710120000E4Q00D6001E000200012Q0010011F00023Q001271012000123Q0012710121000E4Q00D6001F000200012Q0010012000023Q001271012100043Q0012710122000F4Q00D60020000200012Q0010012100023Q001271012200063Q0012710123000F4Q00D60021000200012Q0010012200023Q001271012300073Q0012710124000F4Q00D60022000200012Q0010012300023Q001271012400053Q0012710125000F4Q00D60023000200012Q0010012400023Q001271012500083Q0012710126000F4Q00D60024000200012Q0010012500023Q001271012600093Q0012710127000F4Q00D60025000200012Q0010012600023Q0012710127000A3Q0012710128000F4Q00D60026000200012Q0010012700023Q0012710128000B3Q0012710129000F4Q00D60027000200012Q0010012800023Q0012710129000C3Q001271012A000F4Q00D60028000200012Q0010012900023Q001271012A000D3Q001271012B000F4Q00D60029000200012Q0010012A00023Q001271012B000E3Q001271012C000F4Q00D6002A000200012Q0010012B00023Q001271012C000F3Q001271012D000F4Q00D6002B000200012Q0010012C00023Q001271012D00103Q001271012E000F4Q00D6002C000200012Q0010012D00023Q001271012E00113Q001271012F000F4Q00D6002D000200012Q0010012E00023Q001271012F00123Q0012710130000F4Q00D6002E000200012Q00D60002002C00010012FA000300134Q0058000400024Q004701030002000500043A012Q00CE00012Q001001085Q0030360108000B001400302Q0008000C00154Q000900023Q00202Q000A0007000C00202Q000A000A00164Q000A3Q000A00202Q000B0007000D00202Q000B000B00164Q000B0001000B4Q00090002000100101D0108000D000900302B0008000E000B00302B0008000F000B00302B00080017000A0012FA000900184Q0058000A00084Q0044010900020001000614010300BC0001000200043A012Q00BC00012Q00573Q00017Q00183Q0003083Q004765744C6F63616C03053Q00706F735F7803053Q00706F735F79026Q001CC0026Q0010C0026Q0018C0026Q0014C0026Q0008C0027Q00C0026Q00F0BF028Q00026Q00F03F027Q0040026Q000840026Q001040026Q001440026Q001840026Q001C4003063Q00697061697273030A3Q004F6E5061727469636C65026Q003240026Q002Q4003053Q006E65746964030B3Q0053656E645661726C69737400D13Q0012FA3Q00014Q0096012Q000100020020CC5Q00020012FA000100014Q00962Q01000100020020CC0001000100032Q00100102001B4Q0010010300023Q001271010400043Q001271010500054Q00D60003000200012Q0010010400023Q001271010500063Q001271010600054Q00D60004000200012Q0010010500023Q001271010600073Q001271010700054Q00D60005000200012Q0010010600023Q001271010700053Q001271010800054Q00D60006000200012Q0010010700023Q001271010800083Q001271010900054Q00D60007000200012Q0010010800023Q001271010900093Q001271010A00054Q00D60008000200012Q0010010900023Q001271010A000A3Q001271010B00054Q00D60009000200012Q0010010A00023Q001271010B000B3Q001271010C00054Q00D6000A000200012Q0010010B00023Q001271010C000C3Q001271010D00054Q00D6000B000200012Q0010010C00023Q001271010D000D3Q001271010E00054Q00D6000C000200012Q0010010D00023Q001271010E000E3Q001271010F00054Q00D6000D000200012Q0010010E00023Q001271010F000F3Q001271011000054Q00D6000E000200012Q0010010F00023Q001271011000103Q001271011100054Q00D6000F000200012Q0010011000023Q001271011100113Q001271011200054Q00D60010000200012Q0010011100023Q001271011200123Q001271011300054Q00D60011000200012Q0010011200023Q001271011300043Q001271011400084Q00D60012000200012Q0010011300023Q001271011400123Q001271011500084Q00D60013000200012Q0010011400023Q001271011500043Q001271011600094Q00D60014000200012Q0010011500023Q001271011600123Q001271011700094Q00D60015000200012Q0010011600023Q001271011700043Q0012710118000A4Q00D60016000200012Q0010011700023Q001271011800123Q0012710119000A4Q00D60017000200012Q0010011800023Q001271011900043Q001271011A000B4Q00D60018000200012Q0010011900023Q001271011A00123Q001271011B000B4Q00D60019000200012Q0010011A00023Q001271011B00043Q001271011C000C4Q00D6001A000200012Q0010011B00023Q001271011C00123Q001271011D000C4Q00D6001B000200012Q0010011C00023Q001271011D00043Q001271011E000D4Q00D6001C000200012Q0010011D00023Q001271011E00123Q001271011F000D4Q00D6001D000200012Q0010011E00023Q001271011F00043Q0012710120000E4Q00D6001E000200012Q0010011F00023Q001271012000123Q0012710121000E4Q00D6001F000200012Q0010012000023Q001271012100043Q0012710122000F4Q00D60020000200012Q0010012100023Q001271012200063Q0012710123000F4Q00D60021000200012Q0010012200023Q001271012300073Q0012710124000F4Q00D60022000200012Q0010012300023Q001271012400053Q0012710125000F4Q00D60023000200012Q0010012400023Q001271012500083Q0012710126000F4Q00D60024000200012Q0010012500023Q001271012600093Q0012710127000F4Q00D60025000200012Q0010012600023Q0012710127000A3Q0012710128000F4Q00D60026000200012Q0010012700023Q0012710128000B3Q0012710129000F4Q00D60027000200012Q0010012800023Q0012710129000C3Q001271012A000F4Q00D60028000200012Q0010012900023Q001271012A000D3Q001271012B000F4Q00D60029000200012Q0010012A00023Q001271012B000E3Q001271012C000F4Q00D6002A000200012Q0010012B00023Q001271012C000F3Q001271012D000F4Q00D6002B000200012Q0010012C00023Q001271012D00103Q001271012E000F4Q00D6002C000200012Q0010012D00023Q001271012E00113Q001271012F000F4Q00D6002D000200012Q0010012E00023Q001271012F00123Q0012710130000F4Q00D6002E000200012Q00D60002002C00010012FA000300134Q0058000400024Q004701030002000500043A012Q00CE00012Q001001085Q0030360108000B001400302Q0008000C00154Q000900023Q00202Q000A0007000C00202Q000A000A00164Q000A3Q000A00202Q000B0007000D00202Q000B000B00164Q000B0001000B4Q00090002000100101D0108000D000900302B0008000E000B00302B0008000F000B00302B00080017000A0012FA000900184Q0058000A00084Q0044010900020001000614010300BC0001000200043A012Q00BC00012Q00573Q00017Q00033Q00026Q005940025Q0088C340024Q0080842E4104083Q00201C0004000100014Q00043Q000400202Q0005000200024Q00040004000500202Q0005000300034Q0004000400054Q000400028Q00017Q00053Q0003093Q00636F756E7464726F70028Q0003083Q00636F2Q6C6563743203053Q00536C2Q6570026Q004940051C3Q0012FA000500014Q006100068Q000700016Q000800026Q00050008000200122Q000600016Q00078Q000800036Q000900046Q0006000900024Q000500050006000E390102001B0001000500043A012Q001B00010012FA000500034Q004501068Q000700016Q000800026Q00050008000100122Q000500036Q00068Q000700036Q000800046Q00050008000100122Q000500043Q00122Q000600056Q00050002000100046Q00012Q00573Q00017Q000B3Q00034Q00028Q0003063Q00737472696E6703063Q00666F726D617403173Q0060322564206062426C61636B2047656D206C6F636B732003163Q0060322564206065426C75652047656D206C6F636B732003153Q00603225642060634469616D6F6E64206C6F636B732003133Q0060322564206039576F726C64206C6F636B732003043Q006773756203023Q0020212Q033Q00603921042B3Q001271010400013Q000E390102000A00013Q00043A012Q000A00012Q0058000500043Q0012F2000600033Q00202Q00060006000400122Q000700056Q00088Q0006000800024Q000400050006000E39010200130001000100043A012Q001300012Q0058000500043Q0012F2000600033Q00202Q00060006000400122Q000700066Q000800016Q0006000800024Q000400050006000E390102001C0001000200043A012Q001C00012Q0058000500043Q0012F2000600033Q00202Q00060006000400122Q000700076Q000800026Q0006000800024Q000400050006000E39010200250001000300043A012Q002500012Q0058000500043Q0012F2000600033Q00202Q00060006000400122Q000700086Q000800036Q0006000800024Q0004000500060020300005000400090012FD0007000A3Q00122Q0008000B6Q000500086Q00059Q0000017Q00033Q0003043Q006773756203023Q00602E034Q0001063Q00204100013Q000100122Q000300023Q00122Q000400036Q000100046Q00016Q00573Q00017Q002D3Q00030B3Q00776562682Q6F6B55726C3103783Q00682Q7470733A2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F313234363037333532393334322Q383Q39352F5736676566725662393654632D336C52754E694C2Q41355F2Q6662636D5F2D314B657332527968786B584859454E516D525F6F7A31703565566D48684F4B48574537613103133Q00506C617965725F776562682Q6F6B5F6E616D6503083Q004765744C6F63616C03043Q006E616D65030C3Q0072656D6F7665436F6C6F727303143Q00506C617965725F776562682Q6F6B5F776F726C6403083Q00476574576F726C64030B3Q0063752Q72656E7454696D6503023Q006F7303043Q0074696D6503043Q006461746503133Q002125592D256D2D25645425483A254D3A25535A030C3Q007468756D626E61696C55726C03653Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F617661746172732F37353831373532342Q383637362Q353639342F615F64633666313234623Q6634366131362Q6562333538623839383063613136332E6769663F73697A653D3430393603083Q00696D61676555726C03B93Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F313235373938312Q38373830353339353031342F31323632333130332Q39373638372Q382Q39322F7374616E646172645F352E6769663F65783D2Q363938633461622669733D2Q36392Q3733326226686D3D38636162333139666430386566393761633263376430373632666566363866633032343062372Q362Q3562643061332Q3239313836303364613566342Q31376626030F3Q00776562682Q6F6B5061796C6F61643203063Q00737472696E6703063Q00666F726D617403ED0A2Q004Q207B0A7Q2022636F6E74656E74223A202223203C613A62676C616E6A69723A2Q31393335323035322Q33342Q3331302Q38393E202Q2A574542482Q4F4B20425920576176652050726F7879202Q2A222C200A7Q2022656D62656473223A205B0A9Q20207B0A9Q204Q20227469746C65223A20223E203C613A62676C616E6A69723A2Q31393335323035322Q33342Q3331302Q38393E202Q2A576562682Q6F6B2042544B20576176652050726F7879202Q2A222C0A9Q204Q2022636F6C6F72223A2036353238302C0A9Q204Q20227468756D626E61696C223A207B0A9Q207Q202275726C223A20222573220A9Q204Q207D2C0A9Q204Q20226669656C6473223A205B0A9Q207Q207B0A9Q209Q2020226E616D65223A20223E203C613A62676C616E6A69723A2Q31393335323035322Q33342Q3331302Q38393E202Q2A576F726C642Q2A203C613A62676C616E6A69723A313230333635303137362Q34373934363831323E20222C0A9Q209Q20202276616C7565223A20223E202Q2A602573602Q2A203C613A62676C616E6A69723A2Q3132343833373132343230362Q37363436313E222C0A9Q209Q202022696E6C696E65223A20747275650A9Q207Q207D2C0A9Q207Q207B0A9Q209Q2020226E616D65223A20223E203C613A62676C616E6A69723A2Q31393335323035322Q33342Q3331302Q38393E202Q2A486F737465722Q2A203C3A62676C616E6A69723A312Q32363435393332353237393736382Q36373E222C0A9Q209Q20202276616C7565223A20223E202Q2A602573602Q2A2Q203C613A62676C616E6A69723A2Q3132343833373132343230362Q37363436313E222C0A9Q209Q202022696E6C696E65223A20747275650A9Q207Q207D0A9Q204Q205D0A9Q20207D2C0A9Q20207B0A9Q204Q2022636F6C6F72223A2036353238302C0A9Q204Q20226669656C6473223A205B0A9Q207Q207B0A9Q209Q2020226E616D65223A20223E203C613A62676C616E6A69723A2Q31393335323035322Q33342Q3331302Q38393E202Q2A4175746F2D44726F702D546F2D57692Q6E65722Q2A203C613A62676C616E6A69723A2Q31372Q332Q34302Q363335323731373933363E20222C0A9Q209Q20202276616C7565223A20223E202Q2A25732Q2A2Q20222C0A9Q209Q202022696E6C696E65223A20747275650A9Q207Q207D2C0A9Q207Q207B0A9Q209Q2020226E616D65223A20223E203C613A62676C616E6A69723A2Q31393335323035322Q33342Q3331302Q38393E202Q2A4175746F2D5075742D4368616E642Q2A203C3A62676C3A31323436343735313832313031343Q392Q373E20222C0A9Q209Q20202276616C7565223A20223E202Q2A25732Q2A2Q20222C0A9Q209Q202022696E6C696E65223A20747275650A9Q207Q207D2C0A9Q207Q207B0A9Q209Q2020226E616D65223A20223E203C613A62676C616E6A69723A2Q31393335323035322Q33342Q3331302Q38393E202Q2A426574732Q2A203C613A62676C3A313230343237393633343330353438323739323E222C0A9Q209Q20202276616C7565223A20223E202Q2A602573602Q2A203C613A62676C3A313230343237393633343330353438323739323E20222C0A9Q209Q202022696E6C696E65223A20747275650A9Q207Q207D0A9Q204Q205D0A9Q20207D2C0A9Q20207B0A9Q204Q2022636F6C6F72223A2036353238302C0A9Q204Q20226669656C6473223A205B0A9Q207Q207B0A9Q209Q2020226E616D65223A20223E203C613A62676C616E6A69723A2Q31393335323035322Q33342Q3331302Q38393E202Q2A546F74616C20426574732Q2A203C3A776C733A2Q3133393130343839373539302Q31323331373E20222C0A9Q209Q20202276616C7565223A20223E202Q2A602573602Q2A203C3A776C733A2Q3133393130343839373539302Q31323331373E20222C0A9Q209Q202022696E6C696E65223A20747275650A9Q207Q207D0A9Q204Q205D0A9Q20207D2C0A9Q20207B0A9Q204Q2022636F6C6F72223A2036353238302C0A9Q204Q20226669656C6473223A205B0A9Q207Q207B0A9Q209Q2020226E616D65223A20223E203C613A62676C616E6A69723A2Q31393335323035322Q33342Q3331302Q38393E202Q2A506F736974696F6E732042544B2Q2A203C613A62676C3A313230343237393633343330353438323739323E222C0A9Q209Q20202276616C7565223A20223E202Q2A4C65667420506C61796572203C3A62676C616E6A69723A312Q32363435393332353237393736382Q36373E203A2Q2A5C6E3E202Q2A605B25732C25735D602Q2A5C6E5C6E3E202Q2A526967687420506C61796572203C3A62676C616E6A69723A312Q32363435393332353237393736382Q36373E203A2Q2A5C6E3E202Q2A605B25732C25735D602Q2A5C6E5C6E3E202Q2A4C6566742047656D2041726561203C3A62676C616E6A69723A313039333033323130352Q37343136323032313E203A2Q2A5C6E3E202Q2A605B25732C25735D5C6E3E205B25732C25735D5C6E3E205B25732C25735D602Q2A5C6E5C6E3E202Q2A52696768742047656D2041726561203C3A62676C616E6A69723A313039333033323130352Q37343136323032313E203A202Q2A5C6E3E202Q2A605B25732C25735D5C6E3E205B25732C25735D5C6E3E205B25732C25735D602Q2A222C0A9Q209Q202022696E6C696E65223A2066616C73650A9Q207Q207D0A9Q204Q205D0A9Q20207D2C0A9Q20207B0A9Q204Q2022696D616765223A207B0A9Q207Q202275726C223A20222573220A9Q204Q207D2C0A9Q204Q202274696D657374616D70223A20222573220A9Q20207D0A7Q205D0A4Q207D0A4Q2003023Q00617703293Q00456E61626C6564203C613A62676C616E6A69723A2Q3139333133363132353832313Q333537343E2003283Q0044697361626C6564203C613A7265645F646F743A2Q3139333133363133302Q37343830323437323E03023Q00706303283Q00456E61626C6564203C613A62676C616E6A69723A2Q3139333133363132353832313Q333537343E03093Q00636C65616E546578742Q033Q0077696E2Q033Q007731782Q033Q007731792Q033Q007732782Q033Q007732792Q033Q006831782Q033Q006831792Q033Q006832782Q033Q006832792Q033Q006833782Q033Q006833792Q033Q006131782Q033Q006131792Q033Q006132782Q033Q006132792Q033Q006133782Q033Q00613379030B3Q0053656E64576562682Q6F6B00493Q00127C3Q00023Q00124Q00013Q00124Q00048Q0001000200206Q000500206Q00066Q0002000200124Q00033Q00124Q00088Q0001000200206Q000500124Q00073Q00124Q000A3Q00206Q000B6Q0001000200124Q00093Q00124Q000A3Q00206Q000C00122Q0001000D3Q00122Q000200098Q000200029Q0000124Q000F3Q00124Q000E3Q00124Q00113Q00124Q00103Q00124Q00133Q00206Q001400122Q000100153Q00122Q0002000E3Q00122Q000300073Q00122Q000400033Q00122Q000500163Q00062Q0005002600013Q00043A012Q00260001001271010500173Q00062D000500270001000100043A012Q00270001001271010500183Q0012FA000600193Q00068C0106002D00013Q00043A012Q002D00010012710106001A3Q00062D0006002E0001000100043A012Q002E0001001271010600183Q0012FA0007001B3Q0012FA0008001C3Q0012FA0009001D3Q0012FA000A001E3Q0012FA000B001F3Q0012FA000C00203Q0012FA000D00213Q0012FA000E00223Q0012FA000F00233Q0012FA001000243Q0012FA001100253Q0012FA001200263Q00124B011300273Q00122Q001400283Q00122Q001500293Q00122Q0016002A3Q00122Q0017002B3Q00122Q0018002C3Q00122Q001900106Q001A9Q00001A000200124Q00123Q0012FA3Q002D3Q0012FA000100013Q0012FA000200124Q00EA3Q000200012Q00573Q00017Q00103Q0003063Q00652Q6665637403063Q00697061697273026Q005640026Q00F03F027Q0040025Q00805C4003053Q00706169727303093Q00636F756E7464726F7003023Q00574C03023Q00444C2Q033Q0042474C03043Q002Q42474C03093Q0052756E54687265616403143Q0073686F77436F2Q6C6563746564456E61626C6564030A3Q0053656E645061636B657403463Q00616374696F6E7C696E7075740A746578747C60775B60635761766550726F787960775D2028776C292060344265747320617265206E6F74207468652073616D65212028776C29046F3Q0012FA000400013Q00068C0104002100013Q00043A012Q002100010012FA000400024Q0010010500024Q0010010600024Q005800076Q0058000800014Q00D60006000200012Q0010010700024Q0058000800024Q0058000900034Q00D60007000200012Q00D60005000200012Q004701040002000600043A012Q001F00012Q005900095Q001221010A00033Q00202Q000B0008000400202Q000C000800054Q0009000C00014Q00095Q00122Q000A00063Q00202Q000B0008000400202Q000C000800054Q0009000C00014Q00095Q00122Q000A00063Q00202Q000B0008000400202Q000C000800054Q0009000C0001000614010400100001000200043A012Q001000012Q001001045Q0012FA000500074Q0059000600014Q004701050002000700043A012Q003300012Q0010010A00013Q0012ED000B00086Q000C00096Q000D8Q000E00016Q000B000E000200122Q000C00086Q000D00096Q000E00026Q000F00036Q000C000F6Q000A3Q00012Q003B01040009000A000614010500260001000200043A012Q002600012Q0059000500024Q0059000600013Q0020CC0006000600092Q00840006000400060020CC0006000600042Q0059000700013Q0020CC00070007000A2Q00840007000400070020CC0007000700042Q0059000800013Q0020CC00080008000B2Q00840008000400080020CC0008000800042Q0059000900013Q0020CC00090009000C2Q00840009000400090020CC0009000900044Q0005000900022Q0059000600024Q0059000700013Q0020CC0007000700092Q00840007000400070020CC0007000700052Q0059000800013Q0020CC00080008000A2Q00840008000400080020CC0008000800052Q0059000900013Q0020CC00090009000B2Q00840009000400090020CC0009000900052Q0059000A00013Q0020CC000A000A000C2Q0084000A0004000A0020CC000A000A00054Q0006000A0002000668000500680001000600043A012Q006800010012FA0007000D3Q00068901083Q000100092Q00593Q00014Q00593Q00034Q00588Q00583Q00014Q00583Q00024Q00583Q00034Q00593Q00044Q00583Q00044Q00598Q004401070002000100043A012Q006E00012Q0005010700013Q00123D0107000E3Q00122Q0007000F3Q00122Q000800053Q00122Q000900106Q0007000900012Q00573Q00013Q00013Q003B3Q0003053Q007061697273030A3Q00436865636B4C6F636B7303043Q002Q42474C026Q00F03F2Q033Q0042474C03023Q00444C03023Q00574C03053Q00536C2Q6570025Q00408F40030A3Q0053656E645061636B6574027Q004003363Q00616374696F6E7C696E7075740A746578747C60775B2060635761766550726F78796077205D2028776C29206039426574732060623A2003053Q002028776C29030D3Q004F6E546578744F7665726C6179030B3Q006039426574732060623A202Q033Q006C6F6703013Q002003063Q00652Q66656374026Q003D4003083Q004765744C6F63616C03053Q00706F735F78026Q00244003053Q00706F735F79026Q002E4003093Q00636C65616E5465787403043Q006773756203083Q00605B62636532395D034Q0003023Q00696F03043Q006F70656E03083Q0066696C652E74787403013Q007703053Q00777269746503063Q00426574733A2003053Q00636C6F73652Q033Q0077696E026Q005940025Q0088C340024Q0080842E4103403Q00616374696F6E7C696E7075740A746578747C60775B2060635761766550726F78796077205D2028776C29206034546F74616C206039426574732060633A60342003153Q006034546F74616C206039426574732060633A603420030F3Q00207C2060375461782069732060323A2Q033Q0074617803013Q002503023Q00252003063Q004C6F67424554031C3Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C5B03023Q006F7303043Q006461746503053Q0025483A254D03093Q005D2042657473203A20030B3Q007C6C6566747C3234327C0A03143Q0073686F77436F2Q6C6563746564456E61626C656403063Q006474315F786403073Q007370616D616C7703043Q007370616D03073Q00776562682Q6F6B03093Q0052756E54687265616403063Q0062746B77656200B73Q0012FA3Q00014Q005900016Q0047012Q0002000200043A012Q000D00010012FA000500024Q00620005000100012Q0059000500014Q0058000600044Q0059000700024Q0059000800034Q0059000900044Q0059000A00054Q00EA0005000A0001000614012Q00040001000200043A012Q000400012Q00593Q00064Q0083000100076Q00025Q00202Q0002000200034Q00010001000200202Q0001000100044Q000200076Q00035Q00202Q0003000300054Q00020002000300202Q0002000200042Q0083000300076Q00045Q00202Q0004000400064Q00030003000400202Q0003000300044Q000400076Q00055Q00202Q0005000500074Q00040004000500202Q0004000400046Q000400020012FA000100083Q001271010200094Q00442Q01000200010012FA0001000A3Q0012710102000B3Q0012710103000C4Q005800045Q0012710105000D4Q006F0103000300052Q00EA0001000300010012FA0001000E3Q0012710102000F4Q005800036Q006F0102000200032Q00442Q01000200010012FA000100103Q0012710102000F4Q005800036Q006F0102000200032Q00442Q01000200010012FA0001000E3Q0012710102000F4Q005800035Q001271010400114Q006F0102000200042Q00442Q01000200010012FA000100123Q00068C2Q01004D00013Q00043A012Q004D00012Q0059000100083Q001271010200133Q0012FA000300144Q00960103000100020020CC0003000300150020790103000300160012FA000400144Q00960104000100020020CC0004000400170020790104000400182Q00EA00010004000100203000013Q001A0012E00003001B3Q00122Q0004001C6Q00010004000200122Q000100193Q00122Q0001001D3Q00202Q00010001001E00122Q0002001F3Q00122Q000300206Q00010003000200202Q000200010021001271010400223Q0012FA000500194Q006F0104000400052Q00EA0002000400010020300002000100232Q00440102000200012Q0083000200076Q00035Q00202Q0003000300074Q00020002000300202Q0002000200044Q000300076Q00045Q00202Q0004000400064Q00030003000400202Q00030003000400203C0103000300252Q00F70002000200032Q0059000300074Q005900045Q0020CC0004000400052Q00840003000300040020CC00030003000400203C0103000300262Q00F70002000200032Q0059000300074Q005900045Q0020CC0004000400032Q00840003000300040020CC00030003000400203C0103000300272Q00F700020002000300203C01020002000B00120A000200243Q0012FA000200083Q001271010300094Q00440102000200010012FA0002000A3Q0012B50003000B3Q00122Q000400283Q00122Q000500243Q00122Q0006000D6Q0004000400064Q0002000400010012FA0002000E3Q001271010300293Q0012FA000400243Q0012BA0005002A3Q00122Q0006002B3Q00122Q0007002C6Q0003000300074Q00020002000100122Q0002000E3Q00122Q000300293Q00122Q000400243Q00122Q0005002A3Q00122Q0006002B3Q0012710107002D4Q001F0003000300074Q00020002000100122Q000200103Q00122Q000300293Q00122Q000400243Q00122Q0005002A3Q00122Q0006002B3Q00122Q0007002D6Q0003000300074Q0002000200010012FA0002002E3Q0012710103002F3Q0012FA000400303Q0020CC000400040031001271010500324Q00C6000400020002001271010500334Q005800065Q001271010700344Q00CF00020002000700122Q0002002E6Q000200013Q00122Q000200353Q00122Q000200366Q00020001000100122Q000200373Q00062Q000200B000013Q00043A012Q00B000012Q0005010200013Q00120A000200383Q0012FA000200393Q00068C010200B600013Q00043A012Q00B600010012FA0002003A3Q0012FA0003003B4Q00440102000200012Q00573Q00017Q00063Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F747003163Q00616374696F6E7C696E7075740A7C746578747C2F545003133Q0062752Q746F6E436C69636B65647C74616B653103093Q0052756E54687265616402173Q002659012Q00160001000100043A012Q00160001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102001600013Q00043A012Q001600010012FA000200063Q00029C00036Q00440102000200012Q0005010200014Q0099000200024Q00573Q00013Q00013Q00093Q0003143Q0073686F77436F2Q6C6563746564456E61626C656403043Q007370616D030A3Q0068616E646C65426574732Q033Q007731782Q033Q007731792Q033Q007732782Q033Q0077327903063Q00652Q66656374031C3Q006372656174654C617267655061727469636C65426F78452Q6665637400104Q00277Q00124Q00019Q003Q00124Q00023Q00124Q00033Q00122Q000100043Q00122Q000200053Q00122Q000300063Q00122Q000400078Q0004000100124Q00083Q00064Q000F00013Q00043A012Q000F00010012FA3Q00094Q00623Q000100012Q00573Q00017Q000F3Q0003023Q005F4703023Q004F4E2Q033Q004F2Q4603023Q00603203023Q00603403063Q00737472696E6703063Q00666F726D617403363Q0060775B606320576176652050726F78792060775D2060334160355560235460314F20606325732060234D4F444520257325732060632103023Q00617703133Q004175746F2044726F7020746F2057692Q6E6572030E3Q004175746F20507574204368616E64030A3Q0053656E645061636B6574027Q004003123Q00616374696F6E7C696E7075740A746578747C030D3Q004F6E546578744F7665726C6179032D3Q0012FA000300013Q0012FA000400014Q0084000400044Q0088010400044Q003B01033Q00040012FA000300014Q0084000300033Q00068C0103000C00013Q00043A012Q000C0001001271010300023Q00062D0003000D0001000100043A012Q000D0001001271010300033Q0012FA000400014Q0084000400043Q00068C0104001400013Q00043A012Q00140001001271010400043Q00062D000400150001000100043A012Q00150001001271010400053Q0012FA000500063Q0020CC000500050007001271010600083Q002659012Q001D0001000900043A012Q001D00010012710107000A3Q00062D0007001E0001000100043A012Q001E00010012710107000B4Q0058000800044Q0057010900036Q00050009000200122Q0006000C3Q00122Q0007000D3Q00122Q0008000E6Q000900056Q0008000800094Q00060008000100122Q0006000F6Q000700056Q0006000200014Q000600016Q000600028Q00017Q000B3Q00028Q0003103Q004F6E5061727469636C65452Q66656374026Q00F03F027Q0040026Q002Q40026Q003040026Q000840026Q00104003053Q006E65746964026Q00F0BF030B3Q0053656E645661726C69737403114Q001001033Q000600302B00030001000200101D010300034Q0010010400023Q00203C01050001000500207901050005000600203C0106000200050020790106000600062Q00D600040002000100101D01030004000400304000030007000100302Q00030008000100302Q00030009000A00122Q0004000B6Q000500036Q0004000200016Q00017Q000E3Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F617703163Q00616374696F6E7C696E7075740A7C746578747C2F415703103Q0062752Q746F6E436C69636B65647C617703023Q006177031B3Q004175746F2044726F7020746F2057692Q6E657220456E61626C6564031C3Q004175746F2044726F7020746F2057692Q6E65722044697361626C656403163Q00616374696F6E7C696E7075740A7C746578747C2F706303163Q00616374696F6E7C696E7075740A7C746578747C2F504303103Q0062752Q746F6E436C69636B65647C706303023Q00706303163Q004175746F20507574204368616E6420456E61626C656403173Q004175746F20507574204368616E642044697361626C6564022E3Q002659012Q002D0001000100043A012Q002D0001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102001800013Q00043A012Q001800012Q005900025Q0012DE000300063Q00122Q000400073Q00122Q000500086Q000200056Q00025Q00044Q002D0001002030000200010002001271010400096Q00020004000200062D000200270001000100043A012Q002700010020300002000100020012710104000A6Q00020004000200062D000200270001000100043A012Q002700010020300002000100020012710104000B6Q00020004000200068C0102002D00013Q00043A012Q002D00012Q005900025Q0012710103000C3Q0012710104000D3Q0012710105000E5Q00010200054Q003401026Q00573Q00017Q001D3Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F636703163Q00616374696F6E7C696E7075740A7C746578747C2F434703103Q0062752Q746F6E436C69636B65647C703203043Q007370616D028Q0003053Q00706169727303053Q0074696C6573030A3Q00636F756E7464726F7032026Q005C4003043Q006D61746803053Q00666C2Q6F7203083Q00746F6E756D62657203013Q007803013Q007903063Q0074696C65733203063Q00737472696E6703063Q00666F726D6174033C3Q0028632Q6F6C2960315B4B4952495D6039256460775B605E57494E60775D2D6039256460775B60344C4F534560775D60365B4B414E414E5D2863727929033C3Q00286372792960315B4B4952495D6039256460775B60344C4F534560775D2D6039256460775B605E57494E60775D60365B4B414E414E5D28632Q6F6C2903403Q00286C6F6C2960315B4B4952495D2867656D73296039256460775B603854494560775D2D6039256460775B603854494560775D60365B4B414E414E5D286C6F6C29030A3Q0053656E645061636B657403123Q00616374696F6E7C696E7075740A746578747C030D3Q004F6E546578744F7665726C617903043Q006773756203063Q0025282E2D2529034Q002Q033Q006C6F6702723Q002659012Q00710001000100043A012Q00710001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102007100013Q00043A012Q007100012Q000501025Q00123F010200063Q00122Q000200073Q00122Q000300073Q00122Q000400083Q00122Q000500096Q00040002000600044Q002900010012FA0009000A3Q001227010A000B3Q00122Q000B000C3Q00202Q000B000B000D00122Q000C000E3Q00202Q000D0008000F4Q000C000D6Q000B3Q000200122Q000C000C3Q00202Q000C000C000D00122Q000D000E3Q00202Q000E000800104Q000D000E6Q000C8Q00093Q00024Q000200020009000614010400190001000200043A012Q001900010012FA000400083Q0012FA000500114Q004701040002000600043A012Q003F00010012FA0009000A3Q001227010A000B3Q00122Q000B000C3Q00202Q000B000B000D00122Q000C000E3Q00202Q000D0008000F4Q000C000D6Q000B3Q000200122Q000C000C3Q00202Q000C000C000D00122Q000D000E3Q00202Q000E000800104Q000D000E6Q000C8Q00093Q00024Q0003000300090006140104002F0001000200043A012Q002F00012Q0082010400043Q00064C0003004C0001000200043A012Q004C00010012FA000500123Q00207601050005001300122Q000600146Q000700026Q000800036Q0005000800024Q000400053Q00044Q005D000100064C000200560001000300043A012Q005600010012FA000500123Q00207601050005001300122Q000600156Q000700026Q000800036Q0005000800024Q000400053Q00044Q005D00010012FA000500123Q0020CC000500050013001271010600164Q0058000700024Q0058000800036Q0005000800022Q0058000400053Q0012FA000500173Q001271010600013Q001271010700184Q0058000800044Q006F0107000700082Q00EA0005000700010012FA000500193Q00203000060004001A0012710108001B3Q0012710109001C4Q00A1000600094Q005D00053Q00010012FA0005001D3Q00203000060004001A0012710108001B3Q0012710109001C4Q00A1000600094Q005D00053Q00012Q0005010500014Q0099000500024Q00573Q00017Q00103Q00027Q004003043Q0066696E6403183Q00616374696F6E7C696E7075740A7C746578747C2F73746174031A3Q00616374696F6E7C696E7075740A7C746578747C2F737461747573031A3Q00616374696F6E7C696E7075740A7C746578747C2F53544154555303183Q00616374696F6E7C696E7075740A7C746578747C2F5354415403103Q0062752Q746F6E436C69636B65647C703303023Q00617703023Q00706303283Q0060635354415455532060344157206063416E6420603450432060633A20605E456E61626C6564202103393Q00606353544154555320603441572060343A20605E456E61626C65642021206063416E6420603450432060343A20603444697361626C6564202103393Q00606353544154555320603441572060343A20603444697361626C65642021206063416E6420603450432060343A20605E456E61626C65642021033A3Q00606353544154555320603441572060343A20603444697361626C65642021206063416E6420603450432060343A20603444697361626C6564202103073Q006F7665726D7367030A3Q0053656E645061636B657403273Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D20023B3Q002659012Q003A0001000100043A012Q003A0001002030000200010002001271010400036Q00020004000200062D0002001B0001000100043A012Q001B0001002030000200010002001271010400046Q00020004000200062D0002001B0001000100043A012Q001B0001002030000200010002001271010400056Q00020004000200062D0002001B0001000100043A012Q001B0001002030000200010002001271010400066Q00020004000200062D0002001B0001000100043A012Q001B0001002030000200010002001271010400076Q00020004000200068C0102003A00013Q00043A012Q003A00012Q0082010200023Q0012FA000300083Q00068C0103002400013Q00043A012Q002400010012FA000300093Q00068C0103002400013Q00043A012Q002400010012710102000A3Q00043A012Q002F00010012FA000300083Q00068C0103002900013Q00043A012Q002900010012710102000B3Q00043A012Q002F00010012FA000300093Q00068C0103002E00013Q00043A012Q002E00010012710102000C3Q00043A012Q002F00010012710102000D3Q0012FA0003000E4Q0058000400024Q00440103000200010012FA0003000F3Q001271010400013Q001271010500104Q0058000600024Q006F0105000500062Q00EA0003000500012Q0005010300014Q0099000300024Q00573Q00017Q00063Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F637003163Q00616374696F6E7C696E7075740A7C746578747C2F435003103Q0062752Q746F6E436C69636B65647C703103093Q0052756E54687265616402193Q002659012Q00180001000100043A012Q00180001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102001800013Q00043A012Q001800010012FA000200063Q00068901033Q000100022Q00598Q00593Q00014Q00440102000200012Q0005010200014Q0099000200024Q00573Q00013Q00013Q00163Q00030A3Q0053656E645061636B6574027Q0040034A3Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D206063204F5457205055542060344348414E442028746F6E67756529202867656D73292003073Q006F7665726D736703113Q0060634F5457205055542060344348414E44030D3Q004F6E546578744F7665726C617903133Q006063204F5457205055542060344348414E442003053Q00706169727303053Q0074696C657303063Q0074696C65733203043Q006D61746803053Q00666C2Q6F7203083Q00746F6E756D62657203013Q007803013Q0079026Q005640025Q00805C4003043Q006D6F7665025Q0008B64003053Q00536C2Q6570025Q00406A40025Q00407F40003F3Q0012253Q00013Q00122Q000100023Q00122Q000200038Q0002000100124Q00043Q00122Q000100058Q0002000100124Q00063Q00122Q000100078Q0002000100124Q00086Q000100023Q00122Q000200093Q00122Q0003000A6Q0001000200012Q0047012Q0002000200043A012Q003C00010012FA000500084Q0058000600044Q004701050002000700043A012Q003700010012FA000A000B3Q0020CC000A000A000C0012FA000B000D3Q0020CC000C0009000E2Q000A010B000C4Q00C5000A3Q00020012FA000B000B3Q0020CC000B000B000C0012FA000C000D3Q0020CC000D0009000F2Q000A010C000D4Q00C5000B3Q00022Q0059000C5Q001278000D00106Q000E000A6Q000F000B6Q000C000F00014Q000C5Q00122Q000D00116Q000E000A6Q000F000B6Q000C000F00010012FA000C00124Q0058000D000A4Q0058000E000B4Q00EA000C000E00012Q0059000C00014Q0058000D000A4Q0058000E000B3Q001271010F00134Q00EA000C000F00010012FA000C00143Q001271010D00154Q0044010C00020001000614010500150001000200043A012Q001500010012FA000500143Q001271010600164Q0044010500020001000614012Q00110001000200043A012Q001100012Q00573Q00017Q00293Q0003053Q00706169727303053Q0074696C657303013Q0061030A3Q00636F756E7464726F7032026Q005C4003043Q006D61746803053Q00666C2Q6F7203083Q00746F6E756D62657203013Q007803013Q007903063Q0074696C65733203013Q0062030A3Q0053656E645061636B6574027Q004003223Q00616374696F6E7C696E7075740A746578747C28632Q6F6C2960315B4B4952495D6039030E3Q0060775B605E57494E60775D2D6039031A3Q0060775B60344C4F534560775D60365B4B414E414E5D2863727929030D3Q004F6E546578744F7665726C6179030A3Q0060315B4B4952495D603903153Q0060775B60344C4F534560775D60365B4B414E414E5D03163Q0060775B60344C4F534560775D60365B4B414E414E5D202Q033Q006C6F6703063Q004C6F6757494E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203023Q006F7303043Q006461746503053Q0025483A254D030E3Q0060775D2060315B4B4952495D603903203Q0060775B60344C4F534560775D60365B4B414E414E5D7C6C6566747C3234327C0A03213Q00616374696F6E7C696E7075740A746578747C286372792960315B4B4952495D6039030F3Q0060775B60344C4F534560775D2D6039031A3Q0060775B605E57494E60775D60365B4B414E414E5D28632Q6F6C2903143Q0060775B605E57494E60775D60365B4B414E414E5D03153Q0060775B605E57494E60775D60365B4B414E414E5D20031F3Q0060775B605E57494E60775D60365B4B414E414E5D7C6C6566747C3234327C0A03273Q00616374696F6E7C696E7075740A746578747C286C6F6C2960315B4B4952495D2867656D73296039030E3Q0060775B603854494560775D2D603903193Q0060775B603854494560775D60365B4B414E414E5D286C6F6C2903143Q0060775B603854494560775D60365B4B414E414E5D03153Q0060775B603854494560775D60365B4B414E414E5D20031F3Q0060775B603854494560775D60365B4B414E414E5D7C6C6566747C3234327C0A00C73Q0012FA3Q00013Q0012FA000100024Q0047012Q0002000200043A012Q001600010012FA000500033Q001249010600043Q00122Q000700053Q00122Q000800063Q00202Q00080008000700122Q000900083Q00202Q000A000400094Q0009000A6Q00083Q000200122Q000900063Q00202Q00090009000700122Q000A00083Q00202Q000B0004000A4Q000A000B6Q00098Q00063Q00024Q00050005000600122Q000500033Q000614012Q00040001000200043A012Q000400010012FA3Q00013Q0012FA0001000B4Q0047012Q0002000200043A012Q002E00010012FA0005000C3Q001249010600043Q00122Q000700053Q00122Q000800063Q00202Q00080008000700122Q000900083Q00202Q000A000400094Q0009000A6Q00083Q000200122Q000900063Q00202Q00090009000700122Q000A00083Q00202Q000B0004000A4Q000A000B6Q00098Q00063Q00024Q00050005000600122Q0005000C3Q000614012Q001C0001000200043A012Q001C00010012FA3Q00033Q0012FA0001000C3Q00064C0001006200013Q00043A012Q006200010012FA3Q000D3Q0012712Q01000E3Q0012710102000F3Q0012FA000300033Q001271010400103Q0012FA0005000C3Q001271010600114Q006F0102000200062Q00EA3Q000200010012FA3Q00123Q0012712Q0100133Q0012FA000200033Q0012BA000300103Q00122Q0004000C3Q00122Q000500146Q0001000100056Q0002000100124Q00123Q00122Q000100133Q00122Q000200033Q00122Q000300103Q00122Q0004000C3Q001271010500154Q001F0001000100056Q0002000100124Q00163Q00122Q000100133Q00122Q000200033Q00122Q000300103Q00122Q0004000C3Q00122Q000500146Q0001000100056Q000200010012FA3Q00173Q0012702Q0100183Q00122Q000200193Q00202Q00020002001A00122Q0003001B6Q00020002000200122Q0003001C3Q00122Q000400033Q00122Q000500103Q00122Q0006000C3Q00122Q0007001D4Q006F014Q000700120A3Q00173Q0012FA3Q00033Q0012FA0001000C3Q00064C3Q00940001000100043A012Q009400010012FA3Q000D3Q0012712Q01000E3Q0012710102001E3Q0012FA000300033Q0012710104001F3Q0012FA0005000C3Q001271010600204Q006F0102000200062Q00EA3Q000200010012FA3Q00123Q0012712Q0100133Q0012FA000200033Q0012BA0003001F3Q00122Q0004000C3Q00122Q000500216Q0001000100056Q0002000100124Q00123Q00122Q000100133Q00122Q000200033Q00122Q0003001F3Q00122Q0004000C3Q001271010500224Q001F0001000100056Q0002000100124Q00163Q00122Q000100133Q00122Q000200033Q00122Q0003001F3Q00122Q0004000C3Q00122Q000500216Q0001000100056Q000200010012FA3Q00173Q0012702Q0100183Q00122Q000200193Q00202Q00020002001A00122Q0003001B6Q00020002000200122Q0003001C3Q00122Q000400033Q00122Q0005001F3Q00122Q0006000C3Q00122Q000700234Q006F014Q000700120A3Q00173Q0012FA3Q00033Q0012FA0001000C3Q0006683Q00C60001000100043A012Q00C600010012FA3Q000D3Q0012712Q01000E3Q001271010200243Q0012FA000300033Q001271010400253Q0012FA0005000C3Q001271010600264Q006F0102000200062Q00EA3Q000200010012FA3Q00123Q0012712Q0100133Q0012FA000200033Q0012BA000300253Q00122Q0004000C3Q00122Q000500276Q0001000100056Q0002000100124Q00123Q00122Q000100133Q00122Q000200033Q00122Q000300253Q00122Q0004000C3Q001271010500284Q001F0001000100056Q0002000100124Q00163Q00122Q000100133Q00122Q000200033Q00122Q000300253Q00122Q0004000C3Q00122Q000500276Q0001000100056Q000200010012FA3Q00173Q0012702Q0100183Q00122Q000200193Q00202Q00020002001A00122Q0003001B6Q00020002000200122Q0003001C3Q00122Q000400033Q00122Q000500253Q00122Q0006000C3Q00122Q000700294Q006F014Q000700120A3Q00174Q00573Q00017Q00053Q0003093Q0052756E546872656164030A3Q004D652Q73616765426F78030F3Q004E6F74696669636174696F6E202120030F3Q00436F2Q6C656374696E672047656D7303043Q00496E666F00093Q0012FA3Q00013Q00029C00016Q004A3Q0002000100124Q00023Q00122Q000100033Q00122Q000200043Q00122Q000300058Q000300016Q00013Q00013Q000A3Q0003053Q00706169727303053Q0074696C657303043Q006D61746803053Q00666C2Q6F7203083Q00746F6E756D62657203013Q007803013Q007903083Q00636F2Q6C65637432026Q005C4003063Q0074696C657332002F3Q0012FA3Q00013Q0012FA000100024Q0047012Q0002000200043A012Q001500010012FA000500033Q00204A01050005000400122Q000600053Q00202Q0007000400064Q000600076Q00053Q000200122Q000600033Q00202Q00060006000400122Q000700053Q00202Q0008000400074Q000700086Q00063Q000200122Q000700083Q00122Q000800096Q000900056Q000A00066Q0007000A0001000614012Q00040001000200043A012Q000400010012FA3Q00013Q0012FA0001000A4Q0047012Q0002000200043A012Q002C00010012FA000500033Q00204A01050005000400122Q000600053Q00202Q0007000400064Q000600076Q00053Q000200122Q000600033Q00202Q00060006000400122Q000700053Q00202Q0008000400074Q000700086Q00063Q000200122Q000700083Q00122Q000800096Q000900056Q000A00066Q0007000A0001000614012Q001B0001000200043A012Q001B00012Q00573Q00017Q00013Q0003093Q0052756E54687265616400063Q0012FA3Q00013Q0006892Q013Q000100022Q00598Q00593Q00014Q0044012Q000200012Q00573Q00013Q00013Q005E3Q0003023Q00706303053Q00536C2Q6570025Q00408F40030A3Q0053656E645061636B6574027Q004003503Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2060775B6065204F5457205055542060344348414E442028746F6E67756529202867656D73292060775D03073Q006F7665726D736703133Q00605E204F5457205055542060344348414E4420030A3Q004D652Q73616765426F78030F3Q004E6F74696669636174696F6E202120030D3Q0050752Q74696E67204368616E6403043Q00496E666F031C3Q006372656174654C617267655061727469636C65426F78452Q6665637403053Q00706169727303053Q0074696C657303043Q006D61746803053Q00666C2Q6F7203083Q00746F6E756D62657203013Q007803013Q007903063Q00652Q66656374026Q005640025Q00805C4003043Q006D6F7665025Q0008B640025Q00406A40025Q00407F4003063Q0074696C65733203023Q0061772Q033Q0077696E028Q0003013Q006103013Q006203083Q004765744C6F63616C03053Q00706F735F78026Q002Q4003053Q00706F735F7903083Q0046696E64506174682Q033Q007731782Q033Q0077317903083Q00466163655369646503043Q006C6566742Q033Q00746178026Q00F03F2Q033Q006D6F6B026Q005940025Q00388F4003043Q0044726F7003053Q006972656E67024Q0080842E412Q033Q0062676C025Q0088C34003023Q00646C03023Q00776C03053Q00686173696C03133Q00206062426C61636B2047656D204C6F636B603003023Q00603003013Q002003123Q00206065426C75652047656D204C6F636B603003113Q002060314469616D6F6E64204C6F636B6030030F3Q00206039576F726C64204C6F636B603003313Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2Q20603444726F2Q706564030B3Q002060395461782060323A2003083Q00746F737472696E6703013Q0025030D3Q004F6E546578744F7665726C6179031E3Q0060775B606320576176652050726F78792060775D20603444726F2Q7065642Q033Q006C6F6703093Q00603444726F2Q70656403023Q00252003083Q0044726F2Q7065642003043Q006773756203023Q00602E034Q0003093Q00207C20546178203A2003023Q00747803023Q007479025Q0070974003093Q00436865636B5061746803053Q00726967687403163Q00606357692Q6E657220603973652Q746C65642060342103463Q00616374696F6E7C696E7075740A746578747C2060775B606320576176652050726F78792060775D2Q20606357692Q6E657220603973652Q746C65642060342120286772696E2903453Q00616374696F6E7C696E7075740A746578747C60775B606320576176652050726F78792060775D2Q2060634741532060324D4F524520603447412060325349523F2028776C2903113Q0057692Q6E65722073652Q746C6564202120026Q003D40026Q002440026Q002E4003073Q007370616D616C7703043Q007370616D2Q033Q007732782Q033Q0077327903333Q00616374696F6E7C696E7075740A746578747C2060775B606320576176652050726F78792060775D3Q20603444726F2Q706564031F3Q0060775B606320576176652050726F78792060775D2Q20603444726F2Q706564025Q00409F4000C5022Q0012FA3Q00013Q00068C012Q006D00013Q00043A012Q006D00010012FA3Q00023Q0012712Q0100034Q00743Q0002000100124Q00043Q00122Q000100053Q00122Q000200068Q0002000100124Q00073Q00122Q000100088Q000200010012FA3Q00093Q0012712Q01000A3Q00122C0002000B3Q00122Q0003000C8Q0003000100124Q000D8Q0001000100124Q000E3Q00122Q0001000F8Q0002000200044Q003D00010012FA000500103Q00207900050005001100122Q000600123Q00202Q0007000400134Q000600076Q00053Q000200122Q000600103Q00202Q00060006001100122Q000700123Q00202Q0008000400144Q000700086Q00063Q000200122Q000700153Q00062Q0007003100013Q00043A012Q003100012Q005900075Q001278000800166Q000900056Q000A00066Q0007000A00014Q00075Q00122Q000800176Q000900056Q000A00066Q0007000A00010012FA000700184Q0058000800054Q0058000900064Q00EA0007000900012Q0059000700014Q0058000800054Q0058000900063Q001271010A00194Q00EA0007000A00010012FA000700023Q0012710108001A4Q0044010700020001000614012Q00180001000200043A012Q001800010012FA3Q00023Q0012712Q01001B4Q0044012Q000200010012FA3Q000E3Q0012FA0001001C4Q0047012Q0002000200043A012Q006B00010012FA000500103Q00207900050005001100122Q000600123Q00202Q0007000400134Q000600076Q00053Q000200122Q000600103Q00202Q00060006001100122Q000700123Q00202Q0008000400144Q000700086Q00063Q000200122Q000700153Q00062Q0007005F00013Q00043A012Q005F00012Q005900075Q001278000800166Q000900056Q000A00066Q0007000A00014Q00075Q00122Q000800176Q000900056Q000A00066Q0007000A00010012FA000700184Q0058000800054Q0058000900064Q00EA0007000900012Q0059000700014Q0058000800054Q0058000900063Q001271010A00194Q00EA0007000A00010012FA000700023Q0012710108001A4Q0044010700020001000614012Q00460001000200043A012Q004600010012FA3Q001D3Q00068C012Q00C402013Q00043A012Q00C402010012FA3Q001E3Q000E39011F00C402013Q00043A012Q00C402010012FA3Q00203Q0012FA000100213Q00064C0001009A2Q013Q00043A012Q009A2Q010012FA3Q00224Q00033Q0001000200206Q002300206Q002400124Q00133Q00124Q00228Q0001000200206Q002500206Q002400124Q00143Q00124Q00263Q00122Q000100273Q00122Q000200288Q0002000100124Q00153Q00064Q009200013Q00043A012Q009200012Q00597Q00129B2Q0100163Q00122Q000200273Q00122Q000300288Q000300019Q0000122Q000100173Q00122Q000200273Q00122Q000300288Q000300010012FA3Q00293Q0012712Q01002A4Q0044012Q000200010012FA3Q002B3Q00265B3Q00A40001002C00043A012Q00A400010012FA3Q001E3Q0012440001002B9Q00000100206Q002E00124Q002D3Q00124Q001E3Q00122Q0001001E3Q00122Q0002002B6Q00010001000200202Q00010001002E8Q000100124Q001E3Q0012FA3Q00023Q0012380001002F8Q0002000100124Q00303Q00122Q0001001E8Q0002000100124Q00293Q00122Q0001002A8Q0002000100124Q00103Q00206Q001100122Q0001001E3Q00202Q0001000100326Q0002000200124Q00313Q00124Q00103Q00206Q001100122Q0001001E3Q00202Q0001000100346Q0002000200124Q00333Q00124Q001E3Q00122Q000100333Q00202Q0001000100348Q000100124Q001E3Q00124Q00103Q00206Q001100122Q0001001E3Q00202Q00010001002E6Q0002000200124Q00353Q00124Q001E3Q00206Q002E00124Q00363Q00124Q00313Q00264Q00CF0001001F00043A012Q00CF00010012FA3Q00313Q0012712Q0100384Q006F014Q000100062D3Q00D00001000100043A012Q00D00001001271012Q00393Q0012712Q01003A3Q0012FA000200333Q00265B000200D90001001F00043A012Q00D900010012FA000200333Q0012710103003B4Q006F01020002000300062D000200DA0001000100043A012Q00DA0001001271010200393Q0012710103003A3Q0012FA000400353Q00265B000400E30001001F00043A012Q00E300010012FA000400353Q0012710105003C4Q006F01040004000500062D000400E40001000100043A012Q00E40001001271010400393Q0012710105003A3Q0012FA000600363Q00265B000600ED0001001F00043A012Q00ED00010012FA000600363Q0012710107003D4Q006F01060006000700062D000600EE0001000100043A012Q00EE0001001271010600394Q006F014Q00060012223Q00373Q00124Q00043Q00122Q000100053Q00122Q0002003E3Q00122Q000300373Q00122Q0004003F3Q00122Q000500403Q00122Q0006002B6Q00050002000200122Q000600414Q006F0102000200062Q0067012Q0002000100124Q00423Q00122Q000100433Q00122Q000200373Q00122Q0003003F3Q00122Q000400403Q00122Q0005002B6Q00040002000200122Q000500416Q0001000100052Q0044012Q000200010012FA3Q00443Q001265000100453Q00122Q000200373Q00122Q0003003F3Q00122Q000400403Q00122Q0005002B6Q00040002000200122Q000500416Q0001000100056Q0002000100124Q00423Q001265000100433Q00122Q000200373Q00122Q0003003F3Q00122Q000400403Q00122Q0005002B6Q00040002000200122Q000500466Q0001000100056Q0002000100124Q00093Q0012712Q01000A3Q00124E010200473Q00122Q000300373Q00202Q00030003004800122Q000500493Q00122Q0006004A6Q00030006000200122Q0004004B3Q00122Q000500403Q00122Q0006002B6Q000500020002001271010600414Q009F01020002000600122Q0003000C8Q0003000100124Q00023Q00122Q0001002E8Q0002000100124Q001F3Q00124Q001E3Q00124Q004C3Q00264Q00342Q01001F00043A012Q00342Q010012FA3Q004D3Q00265B3Q005B2Q01001F00043A012Q005B2Q010012FA3Q00023Q00123A0001004E8Q0002000100124Q004F3Q00122Q0001004C3Q00202Q00010001002C00122Q0002004D8Q0002000200064Q004D2Q013Q00043A012Q004D2Q010012FA3Q00263Q0012B00001004C3Q00202Q00010001002C00122Q0002004D8Q0002000100124Q00023Q00122Q0001002F8Q0002000100124Q00303Q00122Q0001002D8Q0002000100124Q00293Q00122Q0001002A8Q0002000100044Q005B2Q010012FA3Q00263Q00128C0001004C3Q00202Q00010001002C00122Q0002004D8Q0002000100124Q00023Q00122Q000100038Q0002000100124Q00303Q00122Q0001002D8Q0002000100124Q00293Q00122Q000100508Q000200010012FA3Q00023Q0012AB0001004E8Q0002000100124Q00263Q00122Q000100133Q00122Q000200148Q0002000100124Q00073Q00122Q000100518Q0002000100124Q00043Q00122Q000100053Q00122Q000200528Q0002000100124Q00023Q00122Q000100038Q0002000100124Q00043Q00122Q000100053Q00122Q000200538Q0002000100124Q00093Q00122Q0001000A3Q00122Q000200543Q00122Q0003000C8Q0003000100124Q00023Q00122Q0001001B8Q0002000100124Q00153Q00064Q00932Q013Q00043A012Q00932Q012Q00597Q001223000100553Q00122Q000200226Q00020001000200202Q00020002002300202Q00020002005600122Q000300226Q00030001000200202Q00030003002500202Q0003000300576Q000300019Q0000122Q000100173Q00122Q000200226Q00020001000200202Q00020002002300202Q00020002005600122Q000300226Q00030001000200202Q00030003002500202Q0003000300576Q0003000100124Q000D8Q000100010012FA3Q00583Q00068C012Q00982Q013Q00043A012Q00982Q012Q0005012Q00013Q00120A3Q00594Q0005012Q00014Q00993Q00023Q0012FA3Q00203Q0012FA000100213Q00064C3Q00BE0201000100043A012Q00BE02010012FA3Q00224Q00033Q0001000200206Q002300206Q002400124Q00133Q00124Q00228Q0001000200206Q002500206Q002400124Q00143Q00124Q00263Q00122Q0001005A3Q00122Q0002005B8Q0002000100124Q00153Q00064Q00B92Q013Q00043A012Q00B92Q012Q00597Q00129B2Q0100163Q00122Q0002005A3Q00122Q0003005B8Q000300019Q0000122Q000100173Q00122Q0002005A3Q00122Q0003005B8Q000300010012FA3Q002B3Q00265B3Q00C82Q01002C00043A012Q00C82Q010012FA3Q001E3Q0012440001002B9Q00000100206Q002E00124Q002D3Q00124Q001E3Q00122Q0001001E3Q00122Q0002002B6Q00010001000200202Q00010001002E8Q000100124Q001E3Q0012FA3Q00023Q001238000100038Q0002000100124Q00303Q00122Q0001001E8Q0002000100124Q00293Q00122Q000100508Q0002000100124Q00103Q00206Q001100122Q0001001E3Q00202Q0001000100326Q0002000200124Q00313Q00124Q00103Q00206Q001100122Q0001001E3Q00202Q0001000100346Q0002000200124Q00333Q00124Q001E3Q00122Q000100333Q00202Q0001000100348Q000100124Q001E3Q00124Q00103Q00206Q001100122Q0001001E3Q00202Q00010001002E6Q0002000200124Q00353Q00124Q001E3Q00206Q002E00124Q00363Q00124Q00313Q00264Q00F32Q01001F00043A012Q00F32Q010012FA3Q00313Q0012712Q0100384Q006F014Q000100062D3Q00F42Q01000100043A012Q00F42Q01001271012Q00393Q0012712Q01003A3Q0012FA000200333Q00265B000200FD2Q01001F00043A012Q00FD2Q010012FA000200333Q0012710103003B4Q006F01020002000300062D000200FE2Q01000100043A012Q00FE2Q01001271010200393Q0012710103003A3Q0012FA000400353Q00265B000400070201001F00043A012Q000702010012FA000400353Q0012710105003C4Q006F01040004000500062D000400080201000100043A012Q00080201001271010400393Q0012710105003A3Q0012FA000600363Q00265B000600110201001F00043A012Q001102010012FA000600363Q0012710107003D4Q006F01060006000700062D000600120201000100043A012Q00120201001271010600394Q006F014Q00060012223Q00373Q00124Q00043Q00122Q000100053Q00122Q0002005C3Q00122Q000300373Q00122Q0004003F3Q00122Q000500403Q00122Q0006002B6Q00050002000200122Q000600414Q006F0102000200062Q0067012Q0002000100124Q00443Q00122Q000100453Q00122Q000200373Q00122Q0003003F3Q00122Q000400403Q00122Q0005002B6Q00040002000200122Q000500416Q0001000100052Q0044012Q000200010012FA3Q00423Q0012650001005D3Q00122Q000200373Q00122Q0003003F3Q00122Q000400403Q00122Q0005002B6Q00040002000200122Q000500416Q0001000100056Q0002000100124Q00423Q0012650001005D3Q00122Q000200373Q00122Q0003003F3Q00122Q000400403Q00122Q0005002B6Q00040002000200122Q000500466Q0001000100056Q0002000100124Q00093Q0012712Q01000A3Q00124E010200473Q00122Q000300373Q00202Q00030003004800122Q000500493Q00122Q0006004A6Q00030006000200122Q0004004B3Q00122Q000500403Q00122Q0006002B6Q000500020002001271010600414Q009F01020002000600122Q0003000C8Q0003000100124Q00023Q00122Q0001002E8Q0002000100124Q001F3Q00124Q001E3Q00124Q004C3Q00264Q00580201001F00043A012Q005802010012FA3Q004D3Q00265B3Q007F0201001F00043A012Q007F02010012FA3Q00023Q00123A000100038Q0002000100124Q004F3Q00122Q0001004C3Q00202Q00010001002C00122Q0002004D8Q0002000200064Q007102013Q00043A012Q007102010012FA3Q00263Q0012B00001004C3Q00202Q00010001002C00122Q0002004D8Q0002000100124Q00023Q00122Q0001002F8Q0002000100124Q00303Q00122Q0001002D8Q0002000100124Q00293Q00122Q0001002A8Q0002000100044Q007F02010012FA3Q00263Q00128C0001004C3Q00202Q00010001002C00122Q0002004D8Q0002000100124Q00023Q00122Q0001002F8Q0002000100124Q00303Q00122Q0001002D8Q0002000100124Q00293Q00122Q000100508Q000200010012FA3Q00023Q0012AB0001005E8Q0002000100124Q00263Q00122Q000100133Q00122Q000200148Q0002000100124Q00073Q00122Q000100518Q0002000100124Q00043Q00122Q000100053Q00122Q000200528Q0002000100124Q00023Q00122Q000100038Q0002000100124Q00043Q00122Q000100053Q00122Q000200538Q0002000100124Q00093Q00122Q0001000A3Q00122Q000200543Q00122Q0003000C8Q0003000100124Q00023Q00122Q0001001B8Q0002000100124Q00153Q00064Q00B702013Q00043A012Q00B702012Q00597Q001223000100553Q00122Q000200226Q00020001000200202Q00020002002300202Q00020002005600122Q000300226Q00030001000200202Q00030003002500202Q0003000300576Q000300019Q0000122Q000100173Q00122Q000200226Q00020001000200202Q00020002002300202Q00020002005600122Q000300226Q00030001000200202Q00030003002500202Q0003000300576Q0003000100124Q000D8Q000100010012FA3Q00583Q00068C012Q00BC02013Q00043A012Q00BC02012Q0005012Q00013Q00120A3Q00594Q0005012Q00014Q00993Q00023Q0012FA3Q00203Q0012FA000100213Q0006683Q00C40201000100043A012Q00C402012Q0005012Q00014Q00993Q00024Q00573Q00017Q000C3Q00027Q004003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F636103163Q00616374696F6E7C696E7075740A7C746578747C2F434103103Q0062752Q746F6E436C69636B65647C636103043Q007370616D03013Q006103013Q0062028Q00030F3Q00636865636B67656D73726573756C74030B3Q00636F2Q6C65637467656D7303073Q00612Q6C67656D7302203Q000E240001000700013Q00043A012Q00070001002030000200010002001271010400036Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400046Q00020004000200062D000200110001000100043A012Q00110001002030000200010002001271010400056Q00020004000200068C0102001F00013Q00043A012Q001F00012Q000501025Q00120A000200063Q001271010200093Q001271010300093Q00120A000300083Q00120A000200073Q0012FA0002000A4Q00620002000100010012FA0002000B4Q00620002000100010012FA0002000C4Q00620002000100012Q0005010200014Q0099000200024Q00573Q00017Q00033Q0003043Q006773756203023Q00602E034Q0001063Q00204100013Q000100122Q000300023Q00122Q000400036Q000100046Q00016Q00573Q00017Q000A3Q00028Q00026Q00F03F034Q0003133Q002060775B60344155544F204C4F53452060775D026Q00184003013Q006003043Q006D61746803063Q0072616E646F6D026Q002240026Q00244001203Q002659012Q00080001000100043A012Q00080001001271012Q00023Q0012712Q0100034Q005800025Q001271010300044Q006F2Q01000100032Q0099000100023Q000E6B0102001600013Q00043A012Q001600010026123Q00160001000500043A012Q001600010012712Q0100063Q001295000200073Q00202Q00020002000800122Q000300013Q00122Q000400096Q00020004000200202Q00033Q000A4Q0001000100034Q000100023Q00044Q001F00010012712Q0100063Q001202010200073Q00202Q00020002000800122Q000300013Q00122Q000400096Q00020004000200202Q00033Q000A4Q0001000100034Q000100024Q00573Q00017Q00063Q00028Q00026Q003340026Q003C4003023Q00603403133Q002060775B60344155544F2057494E60775D6030026Q002440010F3Q00265B3Q00060001000100043A012Q0006000100265B3Q00060001000200043A012Q00060001002659012Q000C0001000300043A012Q000C00010012712Q0100044Q00EF00025Q00122Q000300056Q0001000100034Q000100023Q00044Q000E00010020582Q013Q00062Q0099000100024Q00573Q00017Q00043Q00028Q00026Q00244003043Q006D61746803053Q00666C2Q6F72010D3Q0012712Q0100013Q000E392Q01000B00013Q00043A012Q000B000100205801023Q00022Q00F70001000100020012FA000200033Q0020CC0002000200040020FB00033Q00022Q00C60002000200022Q00583Q00023Q00043A012Q000100012Q0099000100024Q00573Q00017Q000C3Q0003053Q007061697273030A3Q00476574506C617965727303063Q00737472696E672Q033Q0073756203043Q006E616D65026Q0008402Q033Q006C656E027Q004003043Q006D61746803053Q00666C2Q6F7203053Q006E6574696403083Q004765744C6F63616C011D3Q0012C7000100013Q00122Q000200026Q000200016Q00013Q000300044Q001600010012FA000600033Q00201E01060006000400202Q00070005000500122Q000800063Q00122Q000900033Q00202Q00090009000700202Q000A000500054Q00090002000200202Q0009000900084Q00060009000200062Q0006001600013Q00043A012Q001600010012FA000600093Q0020CC00060006000A0020CC00070005000B3Q00010600074Q003401065Q0006142Q0100050001000200043A012Q000500010012FA0001000C4Q00962Q01000100020020CC00010001000B2Q0099000100024Q00573Q00017Q00053Q0003053Q007061697273030A3Q00476574506C617965727303053Q006E6574696403043Q006E616D6503083Q004765744C6F63616C01113Q0012C7000100013Q00122Q000200026Q000200016Q00013Q000300044Q000A00010020CC0006000500030006680006000A00013Q00043A012Q000A00010020CC0006000500042Q0099000600023Q0006142Q0100050001000200043A012Q000500010012FA000100054Q00962Q01000100020020CC0001000100032Q0099000100024Q00573Q00017Q00083Q0003053Q007061697273030A3Q00476574506C617965727303053Q006E6574696403043Q006E616D6503043Q006773756203023Q00602E034Q0003043Q004249425501133Q0012C7000100013Q00122Q000200026Q000200016Q00013Q000300044Q000E00010020CC0006000500030006680006000E00013Q00043A012Q000E00010020CC00060005000400204100060006000500122Q000800063Q00122Q000900076Q000600096Q00065Q0006142Q0100050001000200043A012Q000500010012712Q0100084Q0099000100024Q00573Q00017Q00083Q0003053Q007061697273030A3Q00476574506C617965727303053Q006E6574696403063Q0075736572696403043Q006773756203023Q00602E034Q0003043Q004249425501133Q0012C7000100013Q00122Q000200026Q000200016Q00013Q000300044Q000E00010020CC0006000500030006680006000E00013Q00043A012Q000E00010020CC00060005000400204100060006000500122Q000800063Q00122Q000900076Q000600096Q00065Q0006142Q0100050001000200043A012Q000500010012712Q0100084Q0099000100024Q00573Q00017Q00163Q0003043Q0066696E64031B3Q00616374696F6E7C696E7075740A7C746578747C2F412Q4C5053494E031B3Q00616374696F6E7C696E7075740A7C746578747C2F612Q6C7370696E03123Q0062752Q746F6E436C69636B65647C7370696E030A3Q0052656D6F7665482Q6F6B03183Q004F61646B616964616A7564756138686475383Q61646164031A3Q004F6E5661726C697374616461736461736461736461736461736403113Q006B6F6E746F6C61736461736461732Q313203083Q004F6E4E692Q67657203103Q004F6E4F6B616B64616F646B61736F646B03043Q0072716D65030A3Q0053656E645061636B6574027Q004003553Q00616374696F6E7C696E7075740A746578747C60625B60635761766550726F787960625D2060315260354560334D6040452Q2060315160354560334D6040452060314360355360334E2060334D4F44452060324F4E20030D3Q004F6E546578744F7665726C617903243Q0060325370696E206D6F64652073657420746F20603243534E2026202Q5120262052454D45030C3Q005370696E5F636865636B657203053Q00536C2Q6570026Q00494003073Q00412Q64482Q6F6B03093Q004F6E5661726C697374030A3Q004F6E5661726C69737473023B3Q002030000200010001001271010400026Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400036Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400046Q00020004000200068C0102003A00013Q00043A012Q003A00010012FA000200053Q00127E010300066Q00020002000100122Q000200053Q00122Q000300076Q000200020001001202000200053Q00122Q000300066Q00020002000100122Q000200053Q00122Q000300086Q00020002000100122Q000200053Q00122Q000300096Q00020002000100122Q000200053Q00127E010300076Q00020002000100122Q000200053Q00122Q0003000A6Q0002000200010012FA000200053Q0012710103000B4Q007400020002000100122Q0002000C3Q00122Q0003000D3Q00122Q0004000E6Q00020004000100122Q0002000F3Q00122Q000300106Q00020002000100029C00025Q00123E010200113Q00122Q000200123Q00122Q000300136Q00020002000100122Q000200143Q00122Q000300153Q00122Q000400163Q00122Q000500116Q0002000500014Q000200016Q000200024Q00573Q00013Q00013Q002D3Q00028Q00030C3Q004F6E54616C6B42752Q626C65027Q004003043Q0066696E6403163Q007370756E207468652077682Q656C20616E6420676F74030C3Q0072656D6F7665436F6C6F727303053Q006D61746368031C3Q007370756E207468652077682Q656C20616E6420676F74202825642B29026Q00F03F026Q00F0BF030D3Q004F6E4E616D654368616E67656403083Q004765744C6F63616C03043Q006E616D6503043Q0067737562030F3Q006062255B603425643F25646062255D034Q0003053Q006E65746964030B3Q0053656E645661726C69737403053Q007061697273030A3Q00476574506C6179657273026Q00084003043Q007465787403223Q007370756E207468652077682Q656C20616E6420676F746032202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746032202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746062202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746062202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296077215D030C3Q0060305B603446414B4560305D03093Q0052756E54687265616403083Q00746F6E756D62657203073Q002Q715F6D6F6465030B3Q002Q715F66756E6374696F6E030A3Q0072656D655F6D6F646532030D3Q0072656D655F66756E6374696F6E03093Q0072656D655F6D6F646503173Q0060305B60325245414C60305D20603243534E203A20603203103Q002060302F20603251454D45203A20603203183Q002060302F2060315260354560334D6040452060303A20603201E13Q0020CC00013Q00010026592Q0100E00001000200043A012Q00E000010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q0100E000013Q00043A012Q00E000010020CC00013Q000300207D0001000100064Q00010002000200202Q00020001000700122Q000400086Q00020004000200202Q00033Q000900262Q000300240001000A00043A012Q002400012Q001001035Q00300E01030001000B00122Q0004000C6Q00040001000200202Q00040004000D00202Q00040004000E00122Q0006000F3Q00122Q000700106Q00040007000200102Q00030009000400122Q0004000C6Q00040001000200202Q00040004001100102Q00030011000400122Q000400126Q000500036Q00040002000100044Q00E000010012FA000300133Q0012FA000400144Q00DA000400014Q00AC00033Q000500043A012Q00DE00010020CC00083Q00090020CC000900070011000668000800DE0001000900043A012Q00DE00012Q001001085Q00305E00080001000B00202Q00090007000D00202Q00090009000E00122Q000B000F3Q00122Q000C00106Q0009000C000200102Q00080009000900202Q00090007001100102Q00080011000900122Q000900126Q000A00086Q00090002000100202Q00093Q000100262Q000900DE0001000200043A012Q00DE00010020CC00093Q001500265B000900DE0001000A00043A012Q00DE00010020CC00093Q0003002030000900090004001271010B00056Q0009000B000200068C010900DE00013Q00043A012Q00DE0001001271010900103Q001252000900163Q00202Q00093Q000300202Q00090009000400122Q000B00176Q0009000B000200062Q000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00186Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00196Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001A6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001B6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001C6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001D6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001E6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001F6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00206Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00216Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00226Q0009000B000200068C010900A800013Q00043A012Q00A800010020CC00093Q00030020420009000900064Q0009000200024Q000100096Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q000900233Q00202Q000A3Q000300122Q000B00236Q00090009000B00102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q000900243Q000689010A3Q000100012Q00588Q004401090002000100043A012Q00D200010020CC00093Q00030020300009000900062Q00C60009000200022Q0058000100093Q002030000900010007001271010B00086Q0009000B00022Q0058000200093Q0012FA000900254Q0058000A00024Q00C60009000200022Q0058000200093Q0012EE000900276Q000A00026Q00090002000200122Q000900263Q00122Q000900296Q000A00026Q00090002000200122Q000900283Q00122Q000900273Q00122Q000A00284Q00C600090002000200120A0009002A4Q001001096Q0058000800093Q00302B0008000100020020CC00093Q000900101D0108000900090012710109002B4Q0058000A00023Q001271010B002C3Q0012FA000C00263Q001271010D002D3Q0012FA000E002A4Q006F01090009000E00101D01080003000900302B00080015000A00302B00080011000A0012FA000900124Q0058000A00084Q00440109000200010012FA000900124Q00E4000A3Q000500302Q000A0001000200202Q000B3Q000900102Q000A0009000B00122Q000B00163Q00102Q000A0003000B00302Q000A0015000A00302Q000A0011000A4Q0009000200014Q000900016Q000900023Q000614010300290001000200043A012Q002900012Q00573Q00013Q00013Q00153Q0003053Q00536C2Q6570025Q00408F4003073Q006F7665726D7367031E3Q006065466F756E642046616B65205479706564204E616D652060623A20606303083Q0066696E644E616D6503083Q00746F6E756D626572026Q00F03F027Q004003083Q00476574576F726C6403043Q006E616D6503023Q006F7303043Q0074696D6503043Q006461746503123Q002125592D256D2D25645425483A254D3A255303783Q00682Q7470733A2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F313235363532353Q31302Q333436323831342F7146666364497A3167767768673937427A38433965622Q7446314330775877474F702D49706C5A4C41514542786D33486356414E506D454244346C7A4C45662Q6878433103B93Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F313235373938312Q38373830353339353031342F31323632333130332Q39373638372Q382Q39322F7374616E646172645F352E6769663F65783D2Q363938633461622669733D2Q36392Q3733326226686D3D38636162333139666430386566393761633263376430373632666566363866633032343062372Q362Q3562643061332Q3239313836303364613566342Q3137662603063Q00737472696E6703063Q00666F726D6174036A032Q002Q207B0A5Q2022636F6E74656E74223A20222023203C613A736572753A31323330373Q363937393736343330362Q343E2046414B45205350494E204C4F47203C613A736572753A31323330373Q363937393736343330362Q343E222C0A5Q2022656D62656473223A205B7B0A8Q20227469746C65223A20223C613A726F756C652Q74653A313231333532343531343637363135343339383E2046414B45205350494E204C4F47203C613A726F756C652Q74653A313231333532343531343637363135343339383E222C0A8Q20226465736372697074696F6E223A20223C613A7361643A2Q31323135323436372Q3135303536373533343E2046414B45205350494E204C4F47203C613A7361643A2Q31323135323436372Q3135303536373533343E222C0A8Q2022636F6C6F72223A203136372Q313638302C0A8Q20226669656C6473223A205B0A9Q202Q207B0A9Q205Q20226E616D65223A2022506C6179657220496E666F726D6174696F6E203C3A67745F706C617965723A312Q32363435393332353237393736382Q36373E222C0A9Q205Q202276616C7565223A202246616B652054797065643A202Q2A25732Q2A203C613A616E69736D6172743A363530323831353Q3332373830323338393E5C6E576F726C643A202Q2A25732Q2A203C613A6D6F6E65796D6F757468656D6F6A693A2Q3138363934313338313036333734313437303E5C6E5549443A202Q2A25732Q2A203C3A6C61756768612Q74686973757365723A2Q3138313239342Q3738362Q383733373431303E222C0A9Q205Q2022696E6C696E65223A2066616C73650A9Q202Q207D0A8Q205D2C0A8Q2022696D616765223A207B0A9Q202Q202275726C223A20222573220A8Q207D2C0A8Q2022662Q6F746572223A207B0A9Q202Q202274657874223A202246414B45205350494E204C4F4720222C0A9Q202Q202269636F6E5F75726C223A202Q220A8Q207D2C0A8Q202274696D657374616D70223A20222573220A5Q207D5D0A2Q207D0A2Q2003073Q0066616B656C6F67030B3Q0053656E64576562682Q6F6B00333Q00128E3Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100043Q00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q00024Q0001000100026Q000200019Q0000206Q000800122Q000100096Q00010001000200202Q00010001000A00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q000200122Q0003000B3Q00202Q00030003000C4Q00030001000200122Q0004000B3Q00202Q00040004000D00122Q0005000E6Q000600036Q00040006000200122Q0005000F3Q00122Q000600103Q00122Q000700113Q00202Q00070007001200122Q000800136Q00098Q000A00016Q000B00026Q000C00066Q000D00046Q0007000D000200122Q000800143Q00062Q0008003200013Q00043A012Q003200010012FA000800154Q0058000900054Q0058000A00074Q00EA0008000A00012Q00573Q00017Q00183Q0003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F2Q7103163Q00616374696F6E7C696E7075740A7C746578747C2F2Q5103183Q00616374696F6E7C696E7075740A7C746578747C2F71656D6503183Q00616374696F6E7C696E7075740A7C746578747C2F51454D4503103Q0062752Q746F6E436C69636B65647C6371030A3Q0052656D6F7665482Q6F6B03183Q004F61646B616964616A7564756138686475383Q6164616403113Q006B6F6E746F6C61736461736461732Q313203083Q004F6E4E692Q676572031A3Q004F6E5661726C6973746164617364617364617364617364617364030A3Q004F6E5661726C6973747303043Q0072716D65030A3Q0053656E645061636B6574027Q004003413Q00616374696F6E7C696E7075740A746578747C60625B60635761766550726F787960625D2060335160354560234D6035452060634D4F44452060324F4E2060632120030D3Q004F6E546578744F7665726C6179032F3Q0060625B60635761766550726F787960625D2060335160354560234D6035452060634D4F44452060324F4E2060632120030C3Q005370696E5F636865636B657203053Q00536C2Q6570026Q00494003073Q00412Q64482Q6F6B03093Q004F6E5661726C697374030B3Q004F6E426162693132313231023F3Q002030000200010001001271010400026Q00020004000200062D000200190001000100043A012Q00190001002030000200010001001271010400036Q00020004000200062D000200190001000100043A012Q00190001002030000200010001001271010400046Q00020004000200062D000200190001000100043A012Q00190001002030000200010001001271010400056Q00020004000200062D000200190001000100043A012Q00190001002030000200010001001271010400066Q00020004000200068C0102003E00013Q00043A012Q003E00010012FA000200073Q00127E010300086Q00020002000100122Q000200073Q00122Q000300096Q000200020001001202000200073Q00122Q0003000A6Q00020002000100122Q000200073Q00122Q0003000B6Q00020002000100122Q000200073Q00122Q0003000C6Q00020002000100122Q000200073Q0012710103000D4Q007400020002000100122Q0002000E3Q00122Q0003000F3Q00122Q000400106Q00020004000100122Q000200113Q00122Q000300126Q00020002000100029C00025Q00123E010200133Q00122Q000200143Q00122Q000300156Q00020002000100122Q000200163Q00122Q000300173Q00122Q000400183Q00122Q000500136Q0002000500014Q000200016Q000200024Q00573Q00013Q00013Q00463Q00028Q00030C3Q004F6E54616C6B42752Q626C65027Q004003043Q0066696E6403163Q007370756E207468652077682Q656C20616E6420676F74030C3Q0072656D6F7665436F6C6F727303053Q006D61746368031C3Q007370756E207468652077682Q656C20616E6420676F74202825642B29026Q00F03F026Q00F0BF030D3Q004F6E4E616D654368616E67656403083Q004765744C6F63616C03043Q006E616D6503043Q0067737562030F3Q006062255B603425643F25646062255D034Q0003053Q006E65746964030B3Q0053656E645661726C69737403053Q007061697273030A3Q00476574506C6179657273026Q00084003043Q007465787403223Q007370756E207468652077682Q656C20616E6420676F746032202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746032202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746062202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746062202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296077215D030C3Q0060305B603446414B4560305D03093Q0052756E54687265616403083Q00746F6E756D62657203073Q002Q715F6D6F6465030B3Q0072656D655F6B6F6E746F6C030A3Q0072656D655F6D6F646532030D3Q0072656D655F66756E6374696F6E03093Q0072656D655F6D6F6465030D3Q0060305B60325245414C60305D2003023Q00206003043Q006D61746803063Q0072616E646F6D026Q002240030A3Q0051454D452060623A206003073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203023Q006F7303043Q006461746503053Q0025483A254D03103Q0060775D2060305B60325245414C60305D030B3Q0051454D452060303A206032030B3Q007C6C6566747C3735387C0A2Q033Q00646F6703063Q00737472696E672Q033Q007375622Q033Q00676F74026Q00184003023Q00215D030C3Q00616E616E6973696B6579696D030D3Q006E616D6566726F6D6E6574696403053Q00666C2Q6F7203023Q006065026Q00144003063Q002060345B60652Q033Q0060345D03073Q007370696E616D650135012Q0020CC00013Q00010026592Q0100342Q01000200043A012Q00342Q010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q0100342Q013Q00043A012Q00342Q010020CC00013Q000300207D0001000100064Q00010002000200202Q00020001000700122Q000400086Q00020004000200202Q00033Q000900262Q000300240001000A00043A012Q002400012Q001001035Q00300E01030001000B00122Q0004000C6Q00040001000200202Q00040004000D00202Q00040004000E00122Q0006000F3Q00122Q000700106Q00040007000200102Q00030009000400122Q0004000C6Q00040001000200202Q00040004001100102Q00030011000400122Q000400126Q000500036Q00040002000100044Q00342Q010012FA000300133Q0012FA000400144Q00DA000400014Q00AC00033Q000500043A012Q00322Q010020CC00083Q00090020CC000900070011000668000800322Q01000900043A012Q00322Q012Q001001085Q00305E00080001000B00202Q00090007000D00202Q00090009000E00122Q000B000F3Q00122Q000C00106Q0009000C000200102Q00080009000900202Q00090007001100102Q00080011000900122Q000900126Q000A00086Q00090002000100202Q00093Q000100262Q000900322Q01000200043A012Q00322Q010020CC00093Q001500265B000900322Q01000A00043A012Q00322Q010020CC00093Q0003002030000900090004001271010B00056Q0009000B000200068C010900322Q013Q00043A012Q00322Q01001271010900103Q001252000900163Q00202Q00093Q000300202Q00090009000400122Q000B00176Q0009000B000200062Q000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00186Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00196Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001A6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001B6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001C6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001D6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001E6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001F6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00206Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00216Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00226Q0009000B000200068C010900A800013Q00043A012Q00A800010020CC00093Q00030020420009000900064Q0009000200024Q000100096Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q000900233Q00202Q000A3Q000300122Q000B00236Q00090009000B00102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q000900243Q000689010A3Q000100012Q00588Q004401090002000100043A012Q00262Q010020CC00093Q000300202Q0109000900064Q0009000200024Q000100093Q00202Q00090001000700122Q000B00086Q0009000B00024Q000200093Q00122Q000900256Q000A00026Q0009000200024Q000200093Q00122Q000900276Q000A00026Q00090002000200122Q000900263Q00122Q000900296Q000A00026Q00090002000200122Q000900283Q00122Q000900273Q00122Q000A00286Q00090002000200122Q0009002A6Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q0009002B3Q00202Q000A3Q000300122Q000B002C3Q00122Q000C002D3Q00202Q000C000C002E00122Q000D00153Q00122Q000E002F6Q000C000E000200122Q000D00303Q00122Q000E002D3Q00202Q000E000E002E00122Q000F00153Q00122Q0010002F6Q000E0010000200122Q000F00103Q00122Q001000266Q00090009001000102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q000900313Q00122Q000A00323Q00122Q000B00333Q00202Q000B000B003400122Q000C00356Q000B0002000200122Q000C00363Q00202Q000D3Q000300122Q000E002C3Q00122Q000F002D3Q00202Q000F000F002E00122Q001000153Q00122Q0011002F6Q000F0011000200122Q001000373Q00122Q001100263Q00122Q001200386Q00090009001200122Q000900313Q00122Q0009003A3Q00202Q00090009003B00202Q000A3Q000300202Q000B3Q000300202Q000B000B000400122Q000D003C6Q000B000D000200202Q000B000B003D00202Q000C3Q000300202Q000C000C0004001271010E003E4Q0042010C000E000200202Q000C000C00154Q0009000C000200122Q000900393Q00122Q000900403Q00122Q000A002D3Q00202Q000A000A004100202Q000B3Q00094Q000A000B6Q00093Q000200122Q0009003F3Q00122Q0009003F3Q00202Q00090009000400122Q000B00426Q0009000B000200062Q000900162Q013Q00043A012Q00162Q010012FA0009003A3Q00209000090009003B00122Q000A003F3Q00122Q000B00013Q00122Q000C003F3Q00202Q000C000C000400122Q000E00426Q000C000E000200202Q000C000C00434Q0009000C000200122Q0009003F4Q001001095Q00302301090001000B00122Q000A003F3Q00122Q000B00443Q00122Q000C00393Q00122Q000D00456Q000A000A000D00102Q00090009000A00202Q000A3Q000900102Q00090011000A00122Q000A00463Q00062Q000A00262Q013Q00043A012Q00262Q010012FA000A00124Q0058000B00094Q0044010A000200010012FA000900124Q00E4000A3Q000500302Q000A0001000200202Q000B3Q000900102Q000A0009000B00122Q000B00163Q00102Q000A0003000B00302Q000A0015000A00302Q000A0011000A4Q0009000200014Q000900016Q000900023Q000614010300290001000200043A012Q002900012Q00573Q00013Q00013Q001A3Q0003053Q00536C2Q6570025Q00408F4003073Q006F7665726D7367031E3Q006065466F756E642046616B65205479706564204E616D652060623A20606303083Q0066696E644E616D6503083Q00746F6E756D626572026Q00F03F027Q004003083Q00476574576F726C6403043Q006E616D6503023Q006F7303043Q0074696D6503043Q006461746503123Q002125592D256D2D25645425483A254D3A255303783Q00682Q7470733A2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F313235363532353Q31302Q333436323831342F7146666364497A3167767768673937427A38433965622Q7446314330775877474F702D49706C5A4C41514542786D33486356414E506D454244346C7A4C45662Q6878433103B93Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F313235373938312Q38373830353339353031342F31323632333130332Q39373638372Q382Q39322F7374616E646172645F352E6769663F65783D2Q363938633461622669733D2Q36392Q3733326226686D3D38636162333139666430386566393761633263376430373632666566363866633032343062372Q362Q3562643061332Q3239313836303364613566342Q3137662603063Q00737472696E6703063Q00666F726D6174036A032Q002Q207B0A5Q2022636F6E74656E74223A20222023203C613A736572753A31323330373Q363937393736343330362Q343E2046414B45205350494E204C4F47203C613A736572753A31323330373Q363937393736343330362Q343E222C0A5Q2022656D62656473223A205B7B0A8Q20227469746C65223A20223C613A726F756C652Q74653A313231333532343531343637363135343339383E2046414B45205350494E204C4F47203C613A726F756C652Q74653A313231333532343531343637363135343339383E222C0A8Q20226465736372697074696F6E223A20223C613A7361643A2Q31323135323436372Q3135303536373533343E2046414B45205350494E204C4F47203C613A7361643A2Q31323135323436372Q3135303536373533343E222C0A8Q2022636F6C6F72223A203136372Q313638302C0A8Q20226669656C6473223A205B0A9Q202Q207B0A9Q205Q20226E616D65223A2022506C6179657220496E666F726D6174696F6E203C3A67745F706C617965723A312Q32363435393332353237393736382Q36373E222C0A9Q205Q202276616C7565223A202246616B652054797065643A202Q2A25732Q2A203C613A616E69736D6172743A363530323831353Q3332373830323338393E5C6E576F726C643A202Q2A25732Q2A203C613A6D6F6E65796D6F757468656D6F6A693A2Q3138363934313338313036333734313437303E5C6E5549443A202Q2A25732Q2A203C3A6C61756768612Q74686973757365723A2Q3138313239342Q3738362Q383733373431303E222C0A9Q205Q2022696E6C696E65223A2066616C73650A9Q202Q207D0A8Q205D2C0A8Q2022696D616765223A207B0A9Q202Q202275726C223A20222573220A8Q207D2C0A8Q2022662Q6F746572223A207B0A9Q202Q202274657874223A202246414B45205350494E204C4F4720222C0A9Q202Q202269636F6E5F75726C223A202Q220A8Q207D2C0A8Q202274696D657374616D70223A20222573220A5Q207D5D0A2Q207D0A2Q2003073Q0066616B656C6F67030B3Q0053656E64576562682Q6F6B03073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203053Q0025483A254D03103Q0060775D2060305B603446414B4560305D03173Q0060305B603446414B4560305D7C6C6566747C3735387C0A003F3Q00128E3Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100043Q00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q00024Q0001000100026Q000200019Q0000206Q000800122Q000100096Q00010001000200202Q00010001000A00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q000200122Q0003000B3Q00202Q00030003000C4Q00030001000200122Q0004000B3Q00202Q00040004000D00122Q0005000E6Q000600036Q00040006000200122Q0005000F3Q00122Q000600103Q00122Q000700113Q00202Q00070007001200122Q000800136Q00098Q000A00016Q000B00026Q000C00066Q000D00046Q0007000D000200122Q000800143Q00062Q0008003200013Q00043A012Q003200010012FA000800154Q0058000900054Q0058000A00074Q00EA0008000A00010012FA000800163Q0012A2010900173Q00122Q000A000B3Q00202Q000A000A000D00122Q000B00186Q000A0002000200122Q000B00196Q000C5Q00202Q000C000C000800122Q000D001A6Q00080008000D00122Q000800168Q00017Q00163Q0003043Q0066696E6403163Q00616374696F6E7C696E7075740A7C746578747C2F727103163Q00616374696F6E7C696E7075740A7C746578747C2F525103103Q0062752Q746F6E436C69636B65647C7271030A3Q0052656D6F7665482Q6F6B03113Q006B6F6E746F6C61736461736461732Q3132030B3Q004F6E42616269313231323103183Q004F61646B616964616A7564756138686475383Q6164616403083Q004F6E4E692Q676572031A3Q004F6E5661726C6973746164617364617364617364617364617364030A3Q004F6E5661726C69737473030A3Q0053656E645061636B6574027Q0040034E3Q00616374696F6E7C696E7075740A746578747C60625B60635761766550726F787960625D2060335260354560234D6035452060335160354560234D6035452060634D4F44452060324F4E2060632120030D3Q004F6E546578744F7665726C6179033C3Q0060625B60635761766550726F787960625D2060335260354560234D6035452060335160354560234D6035452060634D4F44452060324F4E2060632120030C3Q005370696E5F636865636B657203053Q00536C2Q6570026Q00494003073Q00412Q64482Q6F6B03093Q004F6E5661726C69737403043Q0072716D6502383Q002030000200010001001271010400026Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400036Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400046Q00020004000200068C0102003700013Q00043A012Q003700010012FA000200053Q00127E010300066Q00020002000100122Q000200053Q00122Q000300076Q000200020001001202000200053Q00122Q000300086Q00020002000100122Q000200053Q00122Q000300096Q00020002000100122Q000200053Q00122Q0003000A6Q00020002000100122Q000200053Q00127E0103000B6Q00020002000100122Q000200053Q00122Q000300066Q0002000200010012FA0002000C3Q0012130103000D3Q00122Q0004000E6Q00020004000100122Q0002000F3Q00122Q000300106Q00020002000100029C00025Q00123E010200113Q00122Q000200123Q00122Q000300136Q00020002000100122Q000200143Q00122Q000300153Q00122Q000400163Q00122Q000500116Q0002000500014Q000200016Q000200024Q00573Q00013Q00013Q00493Q00028Q00030C3Q004F6E54616C6B42752Q626C65027Q004003043Q0066696E6403163Q007370756E207468652077682Q656C20616E6420676F74030C3Q0072656D6F7665436F6C6F727303053Q006D61746368031C3Q007370756E207468652077682Q656C20616E6420676F74202825642B29026Q00F03F026Q00F0BF030D3Q004F6E4E616D654368616E67656403083Q004765744C6F63616C03043Q006E616D6503043Q0067737562030F3Q006062255B603425643F25646062255D034Q0003053Q006E65746964030B3Q0053656E645661726C69737403053Q007061697273030A3Q00476574506C6179657273026Q00084003043Q007465787403223Q007370756E207468652077682Q656C20616E6420676F746032202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746032202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746062202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746062202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296077215D030C3Q0060305B603446414B4560305D03093Q0052756E54687265616403083Q00746F6E756D62657203073Q002Q715F6D6F6465030B3Q0072656D655F6B6F6E746F6C030A3Q0072656D655F6D6F646532030D3Q0072656D655F66756E6374696F6E03093Q0072656D655F6D6F6465030B3Q002Q715F66756E6374696F6E030D3Q0060305B60325245414C60305D2003023Q00206003043Q006D61746803063Q0072616E646F6D026Q002240030A3Q0052454D452060623A206003063Q002060622F2060030A3Q0051454D452060623A206003073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203023Q006F7303043Q006461746503053Q0025483A254D03103Q0060775D2060305B60325245414C60305D030B3Q0052454D452060623A206032030B3Q007C6C6566747C3735387C0A2Q033Q00646F6703063Q00737472696E672Q033Q007375622Q033Q00676F74026Q00184003023Q00215D030C3Q00616E616E6973696B6579696D030D3Q006E616D6566726F6D6E6574696403053Q00666C2Q6F7203023Q006065026Q00144003063Q002060345B60652Q033Q0060345D03073Q007370696E616D650143012Q0020CC00013Q00010026592Q0100422Q01000200043A012Q00422Q010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q0100422Q013Q00043A012Q00422Q010020CC00013Q000300207D0001000100064Q00010002000200202Q00020001000700122Q000400086Q00020004000200202Q00033Q000900262Q000300240001000A00043A012Q002400012Q001001035Q00300E01030001000B00122Q0004000C6Q00040001000200202Q00040004000D00202Q00040004000E00122Q0006000F3Q00122Q000700106Q00040007000200102Q00030009000400122Q0004000C6Q00040001000200202Q00040004001100102Q00030011000400122Q000400126Q000500036Q00040002000100044Q00422Q010012FA000300133Q0012FA000400144Q00DA000400014Q00AC00033Q000500043A012Q00402Q010020CC00083Q00090020CC000900070011000668000800402Q01000900043A012Q00402Q012Q001001085Q00305E00080001000B00202Q00090007000D00202Q00090009000E00122Q000B000F3Q00122Q000C00106Q0009000C000200102Q00080009000900202Q00090007001100102Q00080011000900122Q000900126Q000A00086Q00090002000100202Q00093Q000100262Q000900402Q01000200043A012Q00402Q010020CC00093Q001500265B000900402Q01000A00043A012Q00402Q010020CC00093Q0003002030000900090004001271010B00056Q0009000B000200068C010900402Q013Q00043A012Q00402Q01001271010900103Q001252000900163Q00202Q00093Q000300202Q00090009000400122Q000B00176Q0009000B000200062Q000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00186Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00196Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001A6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001B6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001C6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001D6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001E6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001F6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00206Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00216Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00226Q0009000B000200068C010900A800013Q00043A012Q00A800010020CC00093Q00030020420009000900064Q0009000200024Q000100096Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q000900233Q00202Q000A3Q000300122Q000B00236Q00090009000B00102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q000900243Q000689010A3Q000100012Q00588Q004401090002000100043A012Q00342Q010020CC00093Q00030020300009000900062Q00C60009000200022Q0058000100093Q002030000900010007001271010B00086Q0009000B00022Q0058000200093Q0012FA000900254Q0058000A00024Q00C60009000200022Q0058000200093Q0012EE000900276Q000A00026Q00090002000200122Q000900263Q00122Q000900296Q000A00026Q00090002000200122Q000900283Q00122Q0009002B3Q00122Q000A00284Q00C600090002000200123D0009002A6Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q0009002C3Q00202Q000A3Q000300122Q000B002D3Q00122Q000C002E3Q0020CC000C000C002F001250010D00153Q00122Q000E00306Q000C000E000200122Q000D00313Q00122Q000E002E3Q00202Q000E000E002F00122Q000F00153Q00122Q001000306Q000E0010000200122Q000F00103Q0012FA0010002A3Q00128F011100323Q00122Q0012002E3Q00202Q00120012002F00122Q001300153Q00122Q001400306Q00120014000200122Q001300333Q00122Q0014002E3Q00202Q00140014002F00122Q001500153Q001271011600304Q00D400140016000200122Q001500103Q00122Q001600266Q00090009001600102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q0009000200010012FA000900343Q001271010A00353Q0012FA000B00363Q0020CC000B000B0037001271010C00384Q00C6000B00020002001271010C00393Q0020CC000D3Q0003001271010E002D3Q0012FA000F002E3Q0020CC000F000F002F001271011000013Q0012B8001100306Q000F0011000200122Q0010003A3Q00122Q0011002A3Q00122Q0012003B6Q00090009001200122Q000900343Q00122Q0009003D3Q00202Q00090009003E00202Q000A3Q00030020CC000B3Q0003002030000B000B0004001271010D003F6Q000B000D0002002079010B000B00400020CC000C3Q0003002030000C000C0004001271010E00414Q0042010C000E000200202Q000C000C00154Q0009000C000200122Q0009003C3Q00122Q000900433Q00122Q000A002E3Q00202Q000A000A004400202Q000B3Q00094Q000A000B6Q00093Q000200122Q000900423Q00122Q000900423Q00202Q00090009000400122Q000B00456Q0009000B000200062Q000900242Q013Q00043A012Q00242Q010012FA0009003D3Q00209000090009003E00122Q000A00423Q00122Q000B00013Q00122Q000C00423Q00202Q000C000C000400122Q000E00456Q000C000E000200202Q000C000C00464Q0009000C000200122Q000900424Q001001095Q00302301090001000B00122Q000A00423Q00122Q000B00473Q00122Q000C003C3Q00122Q000D00486Q000A000A000D00102Q00090009000A00202Q000A3Q000900102Q00090011000A00122Q000A00493Q00062Q000A00342Q013Q00043A012Q00342Q010012FA000A00124Q0058000B00094Q0044010A000200010012FA000900124Q00E4000A3Q000500302Q000A0001000200202Q000B3Q000900102Q000A0009000B00122Q000B00163Q00102Q000A0003000B00302Q000A0015000A00302Q000A0011000A4Q0009000200014Q000900016Q000900023Q000614010300290001000200043A012Q002900012Q00573Q00013Q00013Q001A3Q0003053Q00536C2Q6570025Q00408F4003073Q006F7665726D7367031E3Q006065466F756E642046616B65205479706564204E616D652060623A20606303083Q0066696E644E616D6503083Q00746F6E756D626572026Q00F03F027Q004003083Q00476574576F726C6403043Q006E616D6503023Q006F7303043Q0074696D6503043Q006461746503123Q002125592D256D2D25645425483A254D3A255303783Q00682Q7470733A2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F313235363532353Q31302Q333436323831342F7146666364497A3167767768673937427A38433965622Q7446314330775877474F702D49706C5A4C41514542786D33486356414E506D454244346C7A4C45662Q6878433103B93Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F313235373938312Q38373830353339353031342F31323632333130332Q39373638372Q382Q39322F7374616E646172645F352E6769663F65783D2Q363938633461622669733D2Q36392Q3733326226686D3D38636162333139666430386566393761633263376430373632666566363866633032343062372Q362Q3562643061332Q3239313836303364613566342Q3137662603063Q00737472696E6703063Q00666F726D6174039A032Q004Q207B0A7Q2022636F6E74656E74223A20222023203C613A736572753A31323330373Q363937393736343330362Q343E2046414B45205350494E204C4F47203C613A736572753A31323330373Q363937393736343330362Q343E222C0A7Q2022656D62656473223A205B7B0A9Q2020227469746C65223A20223C613A726F756C652Q74653A313231333532343531343637363135343339383E2046414B45205350494E204C4F47203C613A726F756C652Q74653A313231333532343531343637363135343339383E222C0A9Q2020226465736372697074696F6E223A20223C613A7361643A2Q31323135323436372Q3135303536373533343E2046414B45205350494E204C4F47203C613A7361643A2Q31323135323436372Q3135303536373533343E222C0A9Q202022636F6C6F72223A203136372Q313638302C0A9Q2020226669656C6473223A205B0A9Q204Q207B0A9Q207Q20226E616D65223A2022506C6179657220496E666F726D6174696F6E203C3A67745F706C617965723A312Q32363435393332353237393736382Q36373E222C0A9Q207Q202276616C7565223A202246616B652054797065643A202Q2A25732Q2A203C613A616E69736D6172743A363530323831353Q3332373830323338393E5C6E576F726C643A202Q2A25732Q2A203C613A6D6F6E65796D6F757468656D6F6A693A2Q3138363934313338313036333734313437303E5C6E5549443A202Q2A25732Q2A203C3A6C61756768612Q74686973757365723A2Q3138313239342Q3738362Q383733373431303E222C0A9Q207Q2022696E6C696E65223A2066616C73650A9Q204Q207D0A9Q20205D2C0A9Q202022696D616765223A207B0A9Q204Q202275726C223A20222573220A9Q20207D2C0A9Q202022662Q6F746572223A207B0A9Q204Q202274657874223A202246414B45205350494E204C4F4720222C0A9Q204Q202269636F6E5F75726C223A202Q220A9Q20207D2C0A9Q20202274696D657374616D70223A20222573220A7Q207D5D0A4Q207D0A4Q2003073Q0066616B656C6F67030B3Q0053656E64576562682Q6F6B03073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203053Q0025483A254D03103Q0060775D2060305B603446414B4560305D03173Q0060305B603446414B4560305D7C6C6566747C3735387C0A003F3Q00128E3Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100043Q00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q00024Q0001000100026Q000200019Q0000206Q000800122Q000100096Q00010001000200202Q00010001000A00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q000200122Q0003000B3Q00202Q00030003000C4Q00030001000200122Q0004000B3Q00202Q00040004000D00122Q0005000E6Q000600036Q00040006000200122Q0005000F3Q00122Q000600103Q00122Q000700113Q00202Q00070007001200122Q000800136Q00098Q000A00016Q000B00026Q000C00066Q000D00046Q0007000D000200122Q000800143Q00062Q0008003200013Q00043A012Q003200010012FA000800154Q0058000900054Q0058000A00074Q00EA0008000A00010012FA000800163Q0012A2010900173Q00122Q000A000B3Q00202Q000A000A000D00122Q000B00186Q000A0002000200122Q000B00196Q000C5Q00202Q000C000C000800122Q000D001A6Q00080008000D00122Q000800168Q00017Q00163Q0003043Q0066696E6403183Q00616374696F6E7C696E7075740A7C746578747C2F72656D6503183Q00616374696F6E7C696E7075740A7C746578747C2F52454D4503123Q0062752Q746F6E436C69636B65647C72656D65030A3Q0052656D6F7665482Q6F6B03113Q006B6F6E746F6C61736461736461732Q3132030B3Q004F6E42616269313231323103183Q004F61646B616964616A7564756138686475383Q6164616403083Q004F6E4E692Q676572031A3Q004F6E5661726C6973746164617364617364617364617364617364030A3Q004F6E5661726C6973747303043Q0072716D65030A3Q0053656E645061636B6574027Q004003413Q00616374696F6E7C696E7075740A746578747C60625B60635761766550726F787960625D2060335260354560234D6035452060634D4F44452060324F4E2060632120030D3Q004F6E546578744F7665726C6179032F3Q0060625B60635761766550726F787960625D2060335260354560234D6035452060634D4F44452060324F4E2060632120030C3Q005370696E5F636865636B657203053Q00536C2Q6570026Q00494003073Q00412Q64482Q6F6B03093Q004F6E5661726C69737402383Q002030000200010001001271010400026Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400036Q00020004000200062D0002000F0001000100043A012Q000F0001002030000200010001001271010400046Q00020004000200068C0102003700013Q00043A012Q003700010012FA000200053Q00127E010300066Q00020002000100122Q000200053Q00122Q000300076Q000200020001001202000200053Q00122Q000300086Q00020002000100122Q000200053Q00122Q000300096Q00020002000100122Q000200053Q00122Q0003000A6Q00020002000100122Q000200053Q00127E0103000B6Q00020002000100122Q000200053Q00122Q0003000C6Q0002000200010012FA0002000D3Q0012130103000E3Q00122Q0004000F6Q00020004000100122Q000200103Q00122Q000300116Q00020002000100029C00025Q00123E010200123Q00122Q000200133Q00122Q000300146Q00020002000100122Q000200153Q00122Q000300163Q00122Q000400063Q00122Q000500126Q0002000500014Q000200016Q000200024Q00573Q00013Q00013Q00463Q00028Q00030C3Q004F6E54616C6B42752Q626C65027Q004003043Q0066696E6403163Q007370756E207468652077682Q656C20616E6420676F74030C3Q0072656D6F7665436F6C6F727303053Q006D61746368031C3Q007370756E207468652077682Q656C20616E6420676F74202825642B29026Q00F03F026Q00F0BF030D3Q004F6E4E616D654368616E67656403083Q004765744C6F63616C03043Q006E616D6503043Q0067737562030F3Q006062255B603425643F25646062255D034Q0003053Q006E65746964030B3Q0053656E645661726C69737403053Q007061697273030A3Q00476574506C6179657273026Q00084003043Q007465787403223Q007370756E207468652077682Q656C20616E6420676F746032202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746032202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746062202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746062202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296077215D030C3Q0060305B603446414B4560305D03093Q0052756E54687265616403083Q00746F6E756D62657203073Q002Q715F6D6F6465030B3Q002Q715F66756E6374696F6E030A3Q0072656D655F6D6F646532030D3Q0072656D655F66756E6374696F6E03093Q0072656D655F6D6F6465030D3Q0060305B60325245414C60305D2003023Q00206003043Q006D61746803063Q0072616E646F6D026Q002240030A3Q0052454D452060623A206003073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203023Q006F7303043Q006461746503053Q0025483A254D03103Q0060775D2060305B60325245414C60305D030B3Q0052454D452060623A206032030B3Q007C6C6566747C3735387C0A2Q033Q00646F6703063Q00737472696E672Q033Q007375622Q033Q00676F74026Q00184003023Q00215D030C3Q00616E616E6973696B6579696D030D3Q006E616D6566726F6D6E6574696403053Q00666C2Q6F7203023Q006065026Q00144003063Q002060345B60652Q033Q0060345D03073Q007370696E616D650135012Q0020CC00013Q00010026592Q0100342Q01000200043A012Q00342Q010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q0100342Q013Q00043A012Q00342Q010020CC00013Q000300207D0001000100064Q00010002000200202Q00020001000700122Q000400086Q00020004000200202Q00033Q000900262Q000300240001000A00043A012Q002400012Q001001035Q00300E01030001000B00122Q0004000C6Q00040001000200202Q00040004000D00202Q00040004000E00122Q0006000F3Q00122Q000700106Q00040007000200102Q00030009000400122Q0004000C6Q00040001000200202Q00040004001100102Q00030011000400122Q000400126Q000500036Q00040002000100044Q00342Q010012FA000300133Q0012FA000400144Q00DA000400014Q00AC00033Q000500043A012Q00322Q010020CC00083Q00090020CC000900070011000668000800322Q01000900043A012Q00322Q012Q001001085Q00305E00080001000B00202Q00090007000D00202Q00090009000E00122Q000B000F3Q00122Q000C00106Q0009000C000200102Q00080009000900202Q00090007001100102Q00080011000900122Q000900126Q000A00086Q00090002000100202Q00093Q000100262Q000900322Q01000200043A012Q00322Q010020CC00093Q001500265B000900322Q01000A00043A012Q00322Q010020CC00093Q0003002030000900090004001271010B00056Q0009000B000200068C010900322Q013Q00043A012Q00322Q01001271010900103Q001252000900163Q00202Q00093Q000300202Q00090009000400122Q000B00176Q0009000B000200062Q000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00186Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00196Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001A6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001B6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001C6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001D6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001E6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001F6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00206Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00216Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00226Q0009000B000200068C010900A800013Q00043A012Q00A800010020CC00093Q00030020420009000900064Q0009000200024Q000100096Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q000900233Q00202Q000A3Q000300122Q000B00236Q00090009000B00102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q000900243Q000689010A3Q000100012Q00588Q004401090002000100043A012Q00262Q010020CC00093Q000300202Q0109000900064Q0009000200024Q000100093Q00202Q00090001000700122Q000B00086Q0009000B00024Q000200093Q00122Q000900256Q000A00026Q0009000200024Q000200093Q00122Q000900276Q000A00026Q00090002000200122Q000900263Q00122Q000900296Q000A00026Q00090002000200122Q000900283Q00122Q000900273Q00122Q000A00286Q00090002000200122Q0009002A6Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q0009002B3Q00202Q000A3Q000300122Q000B002C3Q00122Q000C002D3Q00202Q000C000C002E00122Q000D00153Q00122Q000E002F6Q000C000E000200122Q000D00303Q00122Q000E002D3Q00202Q000E000E002E00122Q000F00153Q00122Q0010002F6Q000E0010000200122Q000F00103Q00122Q0010002A6Q00090009001000102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q000900313Q00122Q000A00323Q00122Q000B00333Q00202Q000B000B003400122Q000C00356Q000B0002000200122Q000C00363Q00202Q000D3Q000300122Q000E002C3Q00122Q000F002D3Q00202Q000F000F002E00122Q001000013Q00122Q0011002F6Q000F0011000200122Q001000373Q00122Q0011002A3Q00122Q001200386Q00090009001200122Q000900313Q00122Q0009003A3Q00202Q00090009003B00202Q000A3Q000300202Q000B3Q000300202Q000B000B000400122Q000D003C6Q000B000D000200202Q000B000B003D00202Q000C3Q000300202Q000C000C0004001271010E003E4Q0042010C000E000200202Q000C000C00154Q0009000C000200122Q000900393Q00122Q000900403Q00122Q000A002D3Q00202Q000A000A004100202Q000B3Q00094Q000A000B6Q00093Q000200122Q0009003F3Q00122Q0009003F3Q00202Q00090009000400122Q000B00426Q0009000B000200062Q000900162Q013Q00043A012Q00162Q010012FA0009003A3Q00209000090009003B00122Q000A003F3Q00122Q000B00013Q00122Q000C003F3Q00202Q000C000C000400122Q000E00426Q000C000E000200202Q000C000C00434Q0009000C000200122Q0009003F4Q001001095Q00302301090001000B00122Q000A003F3Q00122Q000B00443Q00122Q000C00393Q00122Q000D00456Q000A000A000D00102Q00090009000A00202Q000A3Q000900102Q00090011000A00122Q000A00463Q00062Q000A00262Q013Q00043A012Q00262Q010012FA000A00124Q0058000B00094Q0044010A000200010012FA000900124Q00E4000A3Q000500302Q000A0001000200202Q000B3Q000900102Q000A0009000B00122Q000B00163Q00102Q000A0003000B00302Q000A0015000A00302Q000A0011000A4Q0009000200014Q000900016Q000900023Q000614010300290001000200043A012Q002900012Q00573Q00013Q00013Q001A3Q0003053Q00536C2Q6570025Q00408F4003073Q006F7665726D7367031E3Q006065466F756E642046616B65205479706564204E616D652060623A20606303083Q0066696E644E616D6503083Q00746F6E756D626572026Q00F03F027Q004003083Q00476574576F726C6403043Q006E616D6503023Q006F7303043Q0074696D6503043Q006461746503123Q002125592D256D2D25645425483A254D3A255303783Q00682Q7470733A2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F313235363532353Q31302Q333436323831342F7146666364497A3167767768673937427A38433965622Q7446314330775877474F702D49706C5A4C41514542786D33486356414E506D454244346C7A4C45662Q6878433103B93Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F313235373938312Q38373830353339353031342F31323632333130332Q39373638372Q382Q39322F7374616E646172645F352E6769663F65783D2Q363938633461622669733D2Q36392Q3733326226686D3D38636162333139666430386566393761633263376430373632666566363866633032343062372Q362Q3562643061332Q3239313836303364613566342Q3137662603063Q00737472696E6703063Q00666F726D6174039A032Q004Q207B0A7Q2022636F6E74656E74223A20222023203C613A736572753A31323330373Q363937393736343330362Q343E2046414B45205350494E204C4F47203C613A736572753A31323330373Q363937393736343330362Q343E222C0A7Q2022656D62656473223A205B7B0A9Q2020227469746C65223A20223C613A726F756C652Q74653A313231333532343531343637363135343339383E2046414B45205350494E204C4F47203C613A726F756C652Q74653A313231333532343531343637363135343339383E222C0A9Q2020226465736372697074696F6E223A20223C613A7361643A2Q31323135323436372Q3135303536373533343E2046414B45205350494E204C4F47203C613A7361643A2Q31323135323436372Q3135303536373533343E222C0A9Q202022636F6C6F72223A203136372Q313638302C0A9Q2020226669656C6473223A205B0A9Q204Q207B0A9Q207Q20226E616D65223A2022506C6179657220496E666F726D6174696F6E203C3A67745F706C617965723A312Q32363435393332353237393736382Q36373E222C0A9Q207Q202276616C7565223A202246616B652054797065643A202Q2A25732Q2A203C613A616E69736D6172743A363530323831353Q3332373830323338393E5C6E576F726C643A202Q2A25732Q2A203C613A6D6F6E65796D6F757468656D6F6A693A2Q3138363934313338313036333734313437303E5C6E5549443A202Q2A25732Q2A203C3A6C61756768612Q74686973757365723A2Q3138313239342Q3738362Q383733373431303E222C0A9Q207Q2022696E6C696E65223A2066616C73650A9Q204Q207D0A9Q20205D2C0A9Q202022696D616765223A207B0A9Q204Q202275726C223A20222573220A9Q20207D2C0A9Q202022662Q6F746572223A207B0A9Q204Q202274657874223A202246414B45205350494E204C4F4720222C0A9Q204Q202269636F6E5F75726C223A202Q220A9Q20207D2C0A9Q20202274696D657374616D70223A20222573220A7Q207D5D0A4Q207D0A4Q2003073Q0066616B656C6F67030B3Q0053656E64576562682Q6F6B03073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203053Q0025483A254D03103Q0060775D2060305B603446414B4560305D03173Q0060305B603446414B4560305D7C6C6566747C3735387C0A003F3Q00128E3Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100043Q00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q00024Q0001000100026Q000200019Q0000206Q000800122Q000100096Q00010001000200202Q00010001000A00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q000200122Q0003000B3Q00202Q00030003000C4Q00030001000200122Q0004000B3Q00202Q00040004000D00122Q0005000E6Q000600036Q00040006000200122Q0005000F3Q00122Q000600103Q00122Q000700113Q00202Q00070007001200122Q000800136Q00098Q000A00016Q000B00026Q000C00066Q000D00046Q0007000D000200122Q000800143Q00062Q0008003200013Q00043A012Q003200010012FA000800154Q0058000900054Q0058000A00074Q00EA0008000A00010012FA000800163Q0012A2010900173Q00122Q000A000B3Q00202Q000A000A000D00122Q000B00186Q000A0002000200122Q000B00196Q000C5Q00202Q000C000C000800122Q000D001A6Q00080008000D00122Q000800168Q00017Q00443Q00028Q00030C3Q004F6E54616C6B42752Q626C65027Q004003043Q0066696E6403163Q007370756E207468652077682Q656C20616E6420676F74030C3Q0072656D6F7665436F6C6F727303053Q006D61746368031C3Q007370756E207468652077682Q656C20616E6420676F74202825642B29026Q00F03F026Q00F0BF030D3Q004F6E4E616D654368616E67656403083Q004765744C6F63616C03043Q006E616D6503043Q0067737562030F3Q006062255B603425643F25646062255D034Q0003053Q006E65746964030B3Q0053656E645661726C69737403053Q007061697273030A3Q00476574506C6179657273026Q00084003043Q007465787403223Q007370756E207468652077682Q656C20616E6420676F746032202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746032202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746062202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746062202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296077215D031F3Q007370756E207468652077682Q656C20616E6420676F742060342825642B295D031F3Q007370756E207468652077682Q656C20616E6420676F742060322825642B295D031F3Q007370756E207468652077682Q656C20616E6420676F742060622825642B295D030C3Q0060305B603446414B4560305D03093Q0052756E54687265616403083Q00746F6E756D62657203073Q002Q715F6D6F6465030B3Q002Q715F66756E6374696F6E030A3Q0072656D655F6D6F646532030D3Q0072656D655F66756E6374696F6E03093Q0072656D655F6D6F6465030D3Q0060305B60325245414C60305D2003073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203023Q006F7303043Q006461746503053Q0025483A254D03103Q0060775D2060305B60325245414C60305D03173Q0060305B60325245414C60305D7C6C6566747C3735387C0A2Q033Q00646F6703063Q00737472696E672Q033Q007375622Q033Q00676F74026Q00184003023Q00215D030C3Q00616E616E6973696B6579696D030D3Q006E616D6566726F6D6E6574696403043Q006D61746803053Q00666C2Q6F7203023Q006065026Q00144003063Q002060345B60652Q033Q0060345D03073Q007370696E616D650131012Q0020CC00013Q00010026592Q0100302Q01000200043A012Q00302Q010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q0100302Q013Q00043A012Q00302Q010020CC00013Q000300207D0001000100064Q00010002000200202Q00020001000700122Q000400086Q00020004000200202Q00033Q000900262Q000300240001000A00043A012Q002400012Q001001035Q00300E01030001000B00122Q0004000C6Q00040001000200202Q00040004000D00202Q00040004000E00122Q0006000F3Q00122Q000700106Q00040007000200102Q00030009000400122Q0004000C6Q00040001000200202Q00040004001100102Q00030011000400122Q000400126Q000500036Q00040002000100044Q00302Q010012FA000300133Q0012FA000400144Q00DA000400014Q00AC00033Q000500043A012Q002E2Q010020CC00083Q00090020CC0009000700110006680008002E2Q01000900043A012Q002E2Q012Q001001085Q00305E00080001000B00202Q00090007000D00202Q00090009000E00122Q000B000F3Q00122Q000C00106Q0009000C000200102Q00080009000900202Q00090007001100102Q00080011000900122Q000900126Q000A00086Q00090002000100202Q00093Q000100262Q0009002E2Q01000200043A012Q002E2Q010020CC00093Q001500265B0009002E2Q01000A00043A012Q002E2Q010020CC00093Q0003002030000900090004001271010B00056Q0009000B000200068C0109002E2Q013Q00043A012Q002E2Q01001271010900103Q001252000900163Q00202Q00093Q000300202Q00090009000400122Q000B00176Q0009000B000200062Q000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B00186Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B00196Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B001A6Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B001B6Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B001C6Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B001D6Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B001E6Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B001F6Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B00206Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B00216Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B00226Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B00236Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B00246Q0009000B000200062D000900A20001000100043A012Q00A200010020CC00093Q0003002030000900090004001271010B00256Q0009000B000200068C010900BA00013Q00043A012Q00BA00010020CC00093Q00030020420009000900064Q0009000200024Q000100096Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q000900263Q00202Q000A3Q000300122Q000B00266Q00090009000B00102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q000900273Q000689010A3Q000100012Q00588Q004401090002000100043A012Q00222Q010020CC00093Q00030020C10009000900064Q0009000200024Q000100093Q00202Q00090001000700122Q000B00086Q0009000B00024Q000200093Q00122Q000900286Q000A00026Q0009000200024Q000200093Q00122Q0009002A6Q000A00026Q00090002000200122Q000900293Q00122Q0009002C6Q000A00026Q00090002000200122Q0009002B3Q00122Q0009002A3Q00122Q000A002B6Q00090002000200122Q0009002D6Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q0009002E3Q00202Q000A3Q00034Q00090009000A00102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q0009002F3Q00122Q000A00303Q00122Q000B00313Q00202Q000B000B003200122Q000C00336Q000B0002000200122Q000C00343Q00202Q000D3Q000300122Q000E00356Q00090009000E00122Q0009002F3Q00122Q000900373Q00202Q00090009003800202Q000A3Q000300202Q000B3Q000300202Q000B000B000400122Q000D00396Q000B000D000200202Q000B000B003A00202Q000C3Q000300202Q000C000C000400122Q000E003B6Q000C000E000200202Q000C000C00154Q0009000C000200122Q000900363Q00122Q0009003D3Q00122Q000A003E3Q00202Q000A000A003F00202Q000B3Q00094Q000A000B6Q00093Q000200122Q0009003C3Q00122Q0009003C3Q00202Q00090009000400122Q000B00406Q0009000B000200062Q000900122Q013Q00043A012Q00122Q010012FA000900373Q00209000090009003800122Q000A003C3Q00122Q000B00013Q00122Q000C003C3Q00202Q000C000C000400122Q000E00406Q000C000E000200202Q000C000C00414Q0009000C000200122Q0009003C4Q001001095Q00302301090001000B00122Q000A003C3Q00122Q000B00423Q00122Q000C00363Q00122Q000D00436Q000A000A000D00102Q00090009000A00202Q000A3Q000900102Q00090011000A00122Q000A00443Q00062Q000A00222Q013Q00043A012Q00222Q010012FA000A00124Q0058000B00094Q0044010A000200010012FA000900124Q00E4000A3Q000500302Q000A0001000200202Q000B3Q000900102Q000A0009000B00122Q000B00163Q00102Q000A0003000B00302Q000A0015000A00302Q000A0011000A4Q0009000200014Q000900016Q000900023Q000614010300290001000200043A012Q002900012Q00573Q00013Q00013Q001A3Q0003053Q00536C2Q6570025Q00408F4003073Q006F7665726D7367031E3Q006065466F756E642046616B65205479706564204E616D652060623A20606303083Q0066696E644E616D6503083Q00746F6E756D626572026Q00F03F027Q004003083Q00476574576F726C6403043Q006E616D6503023Q006F7303043Q0074696D6503043Q006461746503123Q002125592D256D2D25645425483A254D3A255303783Q00682Q7470733A2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F313235363532353Q31302Q333436323831342F7146666364497A3167767768673937427A38433965622Q7446314330775877474F702D49706C5A4C41514542786D33486356414E506D454244346C7A4C45662Q6878433103B93Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F313235373938312Q38373830353339353031342F31323632333130332Q39373638372Q382Q39322F7374616E646172645F352E6769663F65783D2Q363938633461622669733D2Q36392Q3733326226686D3D38636162333139666430386566393761633263376430373632666566363866633032343062372Q362Q3562643061332Q3239313836303364613566342Q3137662603063Q00737472696E6703063Q00666F726D6174036A032Q002Q207B0A5Q2022636F6E74656E74223A20222023203C613A736572753A31323330373Q363937393736343330362Q343E2046414B45205350494E204C4F47203C613A736572753A31323330373Q363937393736343330362Q343E222C0A5Q2022656D62656473223A205B7B0A8Q20227469746C65223A20223C613A726F756C652Q74653A313231333532343531343637363135343339383E2046414B45205350494E204C4F47203C613A726F756C652Q74653A313231333532343531343637363135343339383E222C0A8Q20226465736372697074696F6E223A20223C613A7361643A2Q31323135323436372Q3135303536373533343E2046414B45205350494E204C4F47203C613A7361643A2Q31323135323436372Q3135303536373533343E222C0A8Q2022636F6C6F72223A203136372Q313638302C0A8Q20226669656C6473223A205B0A9Q202Q207B0A9Q205Q20226E616D65223A2022506C6179657220496E666F726D6174696F6E203C3A67745F706C617965723A312Q32363435393332353237393736382Q36373E222C0A9Q205Q202276616C7565223A202246616B652054797065643A202Q2A25732Q2A203C613A616E69736D6172743A363530323831353Q3332373830323338393E5C6E576F726C643A202Q2A25732Q2A203C613A6D6F6E65796D6F757468656D6F6A693A2Q3138363934313338313036333734313437303E5C6E5549443A202Q2A25732Q2A203C3A6C61756768612Q74686973757365723A2Q3138313239342Q3738362Q383733373431303E222C0A9Q205Q2022696E6C696E65223A2066616C73650A9Q202Q207D0A8Q205D2C0A8Q2022696D616765223A207B0A9Q202Q202275726C223A20222573220A8Q207D2C0A8Q2022662Q6F746572223A207B0A9Q202Q202274657874223A202246414B45205350494E204C4F4720222C0A9Q202Q202269636F6E5F75726C223A202Q220A8Q207D2C0A8Q202274696D657374616D70223A20222573220A5Q207D5D0A2Q207D0A2Q2003073Q0066616B656C6F67030B3Q0053656E64576562682Q6F6B03073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203053Q0025483A254D03103Q0060775D2060305B603446414B4560305D03173Q0060305B603446414B4560305D7C6C6566747C3735387C0A003F3Q00128E3Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100043Q00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q00024Q0001000100026Q000200019Q0000206Q000800122Q000100096Q00010001000200202Q00010001000A00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q000200122Q0003000B3Q00202Q00030003000C4Q00030001000200122Q0004000B3Q00202Q00040004000D00122Q0005000E6Q000600036Q00040006000200122Q0005000F3Q00122Q000600103Q00122Q000700113Q00202Q00070007001200122Q000800136Q00098Q000A00016Q000B00026Q000C00066Q000D00046Q0007000D000200122Q000800143Q00062Q0008003200013Q00043A012Q003200010012FA000800154Q0058000900054Q0058000A00074Q00EA0008000A00010012FA000800163Q0012A2010900173Q00122Q000A000B3Q00202Q000A000A000D00122Q000B00186Q000A0002000200122Q000B00196Q000C5Q00202Q000C000C000800122Q000D001A6Q00080008000D00122Q000800168Q00017Q00113Q0003043Q0066696E6403193Q00616374696F6E7C696E7075740A7C746578747C2F636865636B030A3Q0052656D6F7665482Q6F6B03183Q004F61646B616964616A7564756138686475383Q6164616403083Q004F6E4E692Q676572030A3Q004F6E5661726C69737473030B3Q004F6E42616269313231323103113Q006B6F6E746F6C61736461736461732Q313203043Q0072716D65030D3Q004F6E546578744F7665726C6179031C3Q0060325370696E206D6F64652073657420746F206032436865636B6572030C3Q005370696E5F636865636B657203053Q00536C2Q6570026Q00494003073Q00412Q64482Q6F6B03093Q004F6E5661726C697374031A3Q004F6E5661726C697374616461736461736461736461736461736402273Q002030000200010001001271010400026Q00020004000200068C0102002600013Q00043A012Q002600010012FA000200033Q00127E010300046Q00020002000100122Q000200033Q00122Q000300056Q000200020001001202000200033Q00122Q000300066Q00020002000100122Q000200033Q00122Q000300076Q00020002000100122Q000200033Q00122Q000300086Q00020002000100122Q000200033Q00127E010300096Q00020002000100122Q0002000A3Q00122Q0003000B6Q00020002000100029C00025Q00123E0102000C3Q00122Q0002000D3Q00122Q0003000E6Q00020002000100122Q0002000F3Q00122Q000300103Q00122Q000400113Q00122Q0005000C6Q0002000500014Q000200016Q000200024Q00573Q00013Q00013Q00413Q00028Q00030C3Q004F6E54616C6B42752Q626C65027Q004003043Q0066696E6403163Q007370756E207468652077682Q656C20616E6420676F74030C3Q0072656D6F7665436F6C6F727303053Q006D61746368031C3Q007370756E207468652077682Q656C20616E6420676F74202825642B29026Q00F03F026Q00F0BF030D3Q004F6E4E616D654368616E67656403083Q004765744C6F63616C03043Q006E616D6503043Q0067737562030F3Q006062255B603425643F25646062255D034Q0003053Q006E65746964030B3Q0053656E645661726C69737403053Q007061697273030A3Q00476574506C6179657273026Q00084003043Q007465787403223Q007370756E207468652077682Q656C20616E6420676F746032202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746032202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060322825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746062202825642B296030215D03233Q007370756E207468652077682Q656C20616E6420676F746062202825642B29603060775D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060622825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F746034202825642B296077215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296030215D03223Q007370756E207468652077682Q656C20616E6420676F742060342825642B296077215D030C3Q0060305B603446414B4560305D03093Q0052756E54687265616403083Q00746F6E756D62657203073Q002Q715F6D6F6465030B3Q002Q715F66756E6374696F6E030A3Q0072656D655F6D6F646532030D3Q0072656D655F66756E6374696F6E03093Q0072656D655F6D6F6465030D3Q0060305B60325245414C60305D2003073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203023Q006F7303043Q006461746503053Q0025483A254D03103Q0060775D2060305B60325245414C60305D03173Q0060305B60325245414C60305D7C6C6566747C3735387C0A2Q033Q00646F6703063Q00737472696E672Q033Q007375622Q033Q00676F74026Q00184003023Q00215D030C3Q00616E616E6973696B6579696D030D3Q006E616D6566726F6D6E6574696403043Q006D61746803053Q00666C2Q6F7203023Q006065026Q00144003063Q002060345B60652Q033Q0060345D03073Q007370696E616D65011F012Q0020CC00013Q00010026592Q01001E2Q01000200043A012Q001E2Q010020CC00013Q0003002030000100010004001271010300056Q00010003000200068C2Q01001E2Q013Q00043A012Q001E2Q010020CC00013Q000300207D0001000100064Q00010002000200202Q00020001000700122Q000400086Q00020004000200202Q00033Q000900262Q000300240001000A00043A012Q002400012Q001001035Q00300E01030001000B00122Q0004000C6Q00040001000200202Q00040004000D00202Q00040004000E00122Q0006000F3Q00122Q000700106Q00040007000200102Q00030009000400122Q0004000C6Q00040001000200202Q00040004001100102Q00030011000400122Q000400126Q000500036Q00040002000100044Q001E2Q010012FA000300133Q0012FA000400144Q00DA000400014Q00AC00033Q000500043A012Q001C2Q010020CC00083Q00090020CC0009000700110006680008001C2Q01000900043A012Q001C2Q012Q001001085Q00305E00080001000B00202Q00090007000D00202Q00090009000E00122Q000B000F3Q00122Q000C00106Q0009000C000200102Q00080009000900202Q00090007001100102Q00080011000900122Q000900126Q000A00086Q00090002000100202Q00093Q000100262Q0009001C2Q01000200043A012Q001C2Q010020CC00093Q001500265B0009001C2Q01000A00043A012Q001C2Q010020CC00093Q0003002030000900090004001271010B00056Q0009000B000200068C0109001C2Q013Q00043A012Q001C2Q01001271010900103Q001252000900163Q00202Q00093Q000300202Q00090009000400122Q000B00176Q0009000B000200062Q000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00186Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00196Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001A6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001B6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001C6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001D6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001E6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B001F6Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00206Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00216Q0009000B000200062D000900900001000100043A012Q009000010020CC00093Q0003002030000900090004001271010B00226Q0009000B000200068C010900A800013Q00043A012Q00A800010020CC00093Q00030020420009000900064Q0009000200024Q000100096Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q000900233Q00202Q000A3Q000300122Q000B00236Q00090009000B00102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q000900243Q000689010A3Q000100012Q00588Q004401090002000100043A012Q00102Q010020CC00093Q00030020C10009000900064Q0009000200024Q000100093Q00202Q00090001000700122Q000B00086Q0009000B00024Q000200093Q00122Q000900256Q000A00026Q0009000200024Q000200093Q00122Q000900276Q000A00026Q00090002000200122Q000900263Q00122Q000900296Q000A00026Q00090002000200122Q000900283Q00122Q000900273Q00122Q000A00286Q00090002000200122Q0009002A6Q00098Q000800093Q00302Q00080001000200202Q00093Q000900102Q00080009000900122Q0009002B3Q00202Q000A3Q00034Q00090009000A00102Q00080003000900302Q00080015000A00302Q00080011000A00122Q000900126Q000A00086Q00090002000100122Q0009002C3Q00122Q000A002D3Q00122Q000B002E3Q00202Q000B000B002F00122Q000C00306Q000B0002000200122Q000C00313Q00202Q000D3Q000300122Q000E00326Q00090009000E00122Q0009002C3Q00122Q000900343Q00202Q00090009003500202Q000A3Q000300202Q000B3Q000300202Q000B000B000400122Q000D00366Q000B000D000200202Q000B000B003700202Q000C3Q000300202Q000C000C000400122Q000E00386Q000C000E000200202Q000C000C00154Q0009000C000200122Q000900333Q00122Q0009003A3Q00122Q000A003B3Q00202Q000A000A003C00202Q000B3Q00094Q000A000B6Q00093Q000200122Q000900393Q00122Q000900393Q00202Q00090009000400122Q000B003D6Q0009000B000200062Q00092Q002Q013Q00043A013Q002Q010012FA000900343Q00209000090009003500122Q000A00393Q00122Q000B00013Q00122Q000C00393Q00202Q000C000C000400122Q000E003D6Q000C000E000200202Q000C000C003E4Q0009000C000200122Q000900394Q001001095Q00302301090001000B00122Q000A00393Q00122Q000B003F3Q00122Q000C00333Q00122Q000D00406Q000A000A000D00102Q00090009000A00202Q000A3Q000900102Q00090011000A00122Q000A00413Q00062Q000A00102Q013Q00043A012Q00102Q010012FA000A00124Q0058000B00094Q0044010A000200010012FA000900124Q00E4000A3Q000500302Q000A0001000200202Q000B3Q000900102Q000A0009000B00122Q000B00163Q00102Q000A0003000B00302Q000A0015000A00302Q000A0011000A4Q0009000200014Q000900016Q000900023Q000614010300290001000200043A012Q002900012Q00573Q00013Q00013Q001A3Q0003053Q00536C2Q6570025Q00408F4003073Q006F7665726D7367031E3Q006065466F756E642046616B65205479706564204E616D652060623A20606303083Q0066696E644E616D6503083Q00746F6E756D626572026Q00F03F027Q004003083Q00476574576F726C6403043Q006E616D6503023Q006F7303043Q0074696D6503043Q006461746503123Q002125592D256D2D25645425483A254D3A255303783Q00682Q7470733A2F646973636F72642E636F6D2F6170692F776562682Q6F6B732F313235363532353Q31302Q333436323831342F7146666364497A3167767768673937427A38433965622Q7446314330775877474F702D49706C5A4C41514542786D33486356414E506D454244346C7A4C45662Q6878433103B93Q00682Q7470733A2F63646E2E646973636F7264612Q702E636F6D2F612Q746163686D656E74732F313235373938312Q38373830353339353031342F31323632333130332Q39373638372Q382Q39322F7374616E646172645F352E6769663F65783D2Q363938633461622669733D2Q36392Q3733326226686D3D38636162333139666430386566393761633263376430373632666566363866633032343062372Q362Q3562643061332Q3239313836303364613566342Q3137662603063Q00737472696E6703063Q00666F726D6174036A032Q002Q207B0A5Q2022636F6E74656E74223A20222023203C613A736572753A31323330373Q363937393736343330362Q343E2046414B45205350494E204C4F47203C613A736572753A31323330373Q363937393736343330362Q343E222C0A5Q2022656D62656473223A205B7B0A8Q20227469746C65223A20223C613A726F756C652Q74653A313231333532343531343637363135343339383E2046414B45205350494E204C4F47203C613A726F756C652Q74653A313231333532343531343637363135343339383E222C0A8Q20226465736372697074696F6E223A20223C613A7361643A2Q31323135323436372Q3135303536373533343E2046414B45205350494E204C4F47203C613A7361643A2Q31323135323436372Q3135303536373533343E222C0A8Q2022636F6C6F72223A203136372Q313638302C0A8Q20226669656C6473223A205B0A9Q202Q207B0A9Q205Q20226E616D65223A2022506C6179657220496E666F726D6174696F6E203C3A67745F706C617965723A312Q32363435393332353237393736382Q36373E222C0A9Q205Q202276616C7565223A202246616B652054797065643A202Q2A25732Q2A203C613A616E69736D6172743A363530323831353Q3332373830323338393E5C6E576F726C643A202Q2A25732Q2A203C613A6D6F6E65796D6F757468656D6F6A693A2Q3138363934313338313036333734313437303E5C6E5549443A202Q2A25732Q2A203C3A6C61756768612Q74686973757365723A2Q3138313239342Q3738362Q383733373431303E222C0A9Q205Q2022696E6C696E65223A2066616C73650A9Q202Q207D0A8Q205D2C0A8Q2022696D616765223A207B0A9Q202Q202275726C223A20222573220A8Q207D2C0A8Q2022662Q6F746572223A207B0A9Q202Q202274657874223A202246414B45205350494E204C4F4720222C0A9Q202Q202269636F6E5F75726C223A202Q220A8Q207D2C0A8Q202274696D657374616D70223A20222573220A5Q207D5D0A2Q207D0A2Q2003073Q0066616B656C6F67030B3Q0053656E64576562682Q6F6B03073Q004C6F675370696E03203Q000A612Q645F6C6162656C5F776974685F69636F6E7C736D612Q6C7C60775B603203053Q0025483A254D03103Q0060775D2060305B603446414B4560305D03173Q0060305B603446414B4560305D7C6C6566747C3735387C0A003F3Q00128E3Q00013Q00122Q000100028Q0002000100124Q00033Q00122Q000100043Q00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q00024Q0001000100026Q000200019Q0000206Q000800122Q000100096Q00010001000200202Q00010001000A00122Q000200053Q00122Q000300066Q00045Q00202Q0004000400074Q000300046Q00023Q000200122Q0003000B3Q00202Q00030003000C4Q00030001000200122Q0004000B3Q00202Q00040004000D00122Q0005000E6Q000600036Q00040006000200122Q0005000F3Q00122Q000600103Q00122Q000700113Q00202Q00070007001200122Q000800136Q00098Q000A00016Q000B00026Q000C00066Q000D00046Q0007000D000200122Q000800143Q00062Q0008003200013Q00043A012Q003200010012FA000800154Q0058000900054Q0058000A00074Q00EA0008000A00010012FA000800163Q0012A2010900173Q00122Q000A000B3Q00202Q000A000A000D00122Q000B00186Q000A0002000200122Q000B00196Q000C5Q00202Q000C000C000800122Q000D001A6Q00080008000D00122Q000800168Q00017Q000E3Q00027Q004003043Q0066696E6403173Q00616374696F6E7C696E7075740A7C746578747C2F6B657903093Q006B65796469616C6F6703143Q0062752Q746F6E436C69636B65647C6765746B657903073Q006F7665726D7367032D3Q00506C65617365207669736974206F757220446973636F72642073657276657220746F206765742061206B65792E03093Q0052756E54687265616403173Q0062752Q746F6E436C69636B65647C7375626D69746B657903053Q006D61746368030B3Q006B65797C285B5E0A5D2B29030B3Q0076616C69646174654B657903263Q006034496E76616C6964206B657960772E20605E506C656173652074727920616761696E60772E03233Q004E6F206B657920656E74657265642E20506C6561736520656E7465722061206B65792E02463Q002659012Q000A0001000100043A012Q000A0001002030000200010002001271010400036Q00020004000200068C0102000A00013Q00043A012Q000A00010012FA000200044Q006200020001000100043A012Q00430001002659012Q001A0001000100043A012Q001A0001002030000200010002001271010400056Q00020004000200068C0102001A00013Q00043A012Q001A00010012FA000200063Q001271010300074Q00440102000200010012FA000200083Q00029C00036Q00440102000200012Q0005010200014Q0099000200023Q00043A012Q00430001002659012Q00430001000100043A012Q00430001002030000200010002001271010400096Q00020004000200068C0102004300013Q00043A012Q0043000100203000020001000A0012710104000B6Q00020004000200068C0102003B00013Q00043A012Q003B00010012FA0003000C4Q0058000400024Q00C600030002000200068C0103003400013Q00043A012Q003400010012FA000300083Q00068901040001000100052Q00598Q00593Q00014Q00593Q00024Q00593Q00034Q00593Q00044Q004401030002000100043A012Q004100010012FA000300063Q0012710104000D4Q00440103000200010012FA000300083Q00029C000400024Q004401030002000100043A012Q004100010012FA000300063Q0012710104000E4Q00440103000200010012FA000300083Q00029C000400034Q00440103000200012Q0005010300014Q0099000300024Q000501026Q0099000200024Q00573Q00013Q00043Q00033Q0003053Q00536C2Q6570025Q0070974003093Q006B65796469616C6F6700063Q0012D73Q00013Q00122Q000100028Q0002000100124Q00038Q000100016Q00017Q00953Q00030A3Q0045646974546F2Q676C65030A3Q005061746846696E646572030B3Q0047656D73436865636B657203073Q00412Q64482Q6F6B03083Q004F6E5061636B657403023Q00783203053Q0072656C6F6703023Q007833030C3Q0072656D6F762Q652Q6665637403023Q007834030D3Q0064657465636B7265737061776E03023Q007835030A3Q0064726F70637573746F6D03023Q007836030D3Q0064726F70576F726C644C6F636B03023Q007837030F3Q0064726F704469616D6F6E644C6F636B03023Q007838030F3Q0064726F70426C756547656D4C6F636B03023Q00783903103Q0064726F70426C61636B47656D4C6F636B2Q033Q00783130030D3Q0064726F7053706C69744C6F636B2Q033Q00782Q3103023Q0072342Q033Q0078313203023Q0072322Q033Q007831332Q033Q006461772Q033Q0078313403023Q0064702Q033Q0078313503023Q00776403093Q004F6E5661726C6973742Q033Q00783136030B3Q00436865636B4C6F636B2Q732Q033Q00783137030E3Q0070752Q6C42414E4B49434B6C6F6C2Q033Q0078313803053Q00682Q6F6B332Q033Q00783139030C3Q00636865636B5F574F524C44322Q033Q0078323003073Q007574696C6974792Q033Q00783231030B3Q007961746175746175616A612Q033Q0078333103083Q00626C6F636B7364622Q033Q00783330030B3Q0074656C657761726E696E672Q033Q00783239030D3Q00626C6F636B736B696E7761726E2Q033Q00783238030E3Q00626C6F636B736B696E7761726E322Q033Q00783237030D3Q0074656C657761726E696E672Q312Q033Q0078323603103Q00626C756567656D6C6F636B6E6F7469662Q033Q00783235030E3Q00556E6B6E6F776E636F2Q6D616E642Q033Q00783234030D3Q006661732Q74656C6570686F6E652Q033Q00783233030F3Q00736F6D657468696E67696C6567616C2Q033Q00782Q3203043Q0074656C652Q033Q0078333203073Q00736B696E6C6F6C2Q033Q0078617003023Q00617003043Q0050752Q6C03403Q0060775B606320576176652050726F78792060775D2Q2060334160355560235460314F20606350552Q4C205752454E43482060234D4F44452060324F4E2060632103413Q0060775B606320576176652050726F78792060775D2Q2060334160355560235460314F20606350552Q4C205752454E43482060234D4F44452060344F2Q4620606321030C3Q0078616B2073686F727463757403023Q00616B03043Q004B69636B033F3Q0060775B606320576176652050726F78792060775D2060334160355560235460314F2060634B49434B205752454E43482060234D4F44452060324F4E2060632103423Q0060775B606320576176652050726F78792060775D2Q2060334160355560235460314F2Q2060634B49434B205752454E43482060234D4F44452060344F2Q4620606321030C3Q007861622073686F727463757403023Q0061622Q033Q0042616E033E3Q0060775B606320576176652050726F78792060775D2060334160355560235460314F20606342414E205752454E43482060234D4F44452060324F4E2060632103413Q0060775B606320576176652050726F78792060775D2060334160355560235460314F2Q20606342414E205752454E43482060234D4F44452060344F2Q4620606320212Q033Q00782Q3303063Q006674726173682Q033Q007833362Q033Q007833352Q033Q0078333403053Q006664726F7003053Q00786C6F616403053Q007361762Q6503053Q00787361766503053Q006C6F612Q64030F3Q0068616E646C655761766550726F787903163Q0068616E646C655761766550726F7879416374696F6E7303063Q0078747062657403023Q0074702Q033Q0078617703023Q0061772Q033Q0078636703023Q00636703053Q00787374617403043Q00737461742Q033Q0078637003023Q0063702Q033Q0078636103023Q00636103083Q0078636F6E736F6C6503073Q00436F6E736F6C6503073Q0078636F6E6669672Q033Q00636667030F3Q0078636F6E666967736176656C6F6164030B3Q00636667736176656C6F6164030D3Q0078636F6E66696773746174757303093Q0063666773746174757303083Q00787365747370616D03073Q007365747370616D03053Q00787370616D03043Q007370616D03083Q00787365746361737403073Q007365746361737403093Q007873746F706361737403083Q0073746F7063617374030E3Q0078737461727462726F6463617374030D3Q00737461727462726F6463617374030D3Q007873657462726F616463617374030C3Q0073657462726F61646361737403083Q0070726F787964756803103Q00656D6F6A6963686174636F2Q6D616E6403193Q00746F2Q676C65636F6C6F7266756C54657874456E61626C656403023Q00637603013Q006C03053Q00536C2Q6570025Q00408F4003063Q006469616C6F6703073Q006F7665726D736703193Q00605E576176652050726F78792049732052752Q6E696E67202103063Q00697061697273027Q0040026Q003440026Q00F03F03063Q00737472696E6703063Q00666F726D617403143Q0064726F70202573207825642073686F727463757403043Q006E616D6503053Q007370616D32030C3Q0073656E64456D6F7469636F6E03063Q007475726E2Q7303093Q00656D6F7469636F6E73007F012Q0012FA3Q00013Q0012712Q0100024Q0005010200014Q00EA3Q000200010012FA3Q00013Q0012712Q0100034Q0005010200014Q004F012Q0002000100124Q00043Q00122Q000100053Q00122Q000200063Q00122Q000300078Q0003000100124Q00043Q00122Q000100053Q00122Q000200083Q00122Q000300094Q004F012Q0003000100124Q00043Q00122Q000100053Q00122Q0002000A3Q00122Q0003000B8Q0003000100124Q00043Q00122Q000100053Q00122Q0002000C3Q00122Q0003000D4Q004F012Q0003000100124Q00043Q00122Q000100053Q00122Q0002000E3Q00122Q0003000F8Q0003000100124Q00043Q00122Q000100053Q00122Q000200103Q00122Q000300114Q004F012Q0003000100124Q00043Q00122Q000100053Q00122Q000200123Q00122Q000300138Q0003000100124Q00043Q00122Q000100053Q00122Q000200143Q00122Q000300154Q004F012Q0003000100124Q00043Q00122Q000100053Q00122Q000200163Q00122Q000300178Q0003000100124Q00043Q00122Q000100053Q00122Q000200183Q00122Q000300194Q004F012Q0003000100124Q00043Q00122Q000100053Q00122Q0002001A3Q00122Q0003001B8Q0003000100124Q00043Q00122Q000100053Q00122Q0002001C3Q00122Q0003001D4Q004F012Q0003000100124Q00043Q00122Q000100053Q00122Q0002001E3Q00122Q0003001F8Q0003000100124Q00043Q00122Q000100053Q00122Q000200203Q00122Q000300214Q004F012Q0003000100124Q00043Q00122Q000100223Q00122Q000200233Q00122Q000300248Q0003000100124Q00043Q00122Q000100053Q00122Q000200253Q00122Q000300264Q004F012Q0003000100124Q00043Q00122Q000100053Q00122Q000200273Q00122Q000300288Q0003000100124Q00043Q00122Q000100223Q00122Q000200293Q00122Q0003002A4Q004F012Q0003000100124Q00043Q00122Q000100053Q00122Q0002002B3Q00122Q0003002C8Q0003000100124Q00043Q00122Q000100053Q00122Q0002002D3Q00122Q0003002E4Q004F012Q0003000100124Q00043Q00122Q000100223Q00122Q0002002F3Q00122Q000300308Q0003000100124Q00043Q00122Q000100223Q00122Q000200313Q00122Q000300324Q004F012Q0003000100124Q00043Q00122Q000100223Q00122Q000200333Q00122Q000300348Q0003000100124Q00043Q00122Q000100223Q00122Q000200353Q00122Q000300364Q004F012Q0003000100124Q00043Q00122Q000100223Q00122Q000200373Q00122Q000300388Q0003000100124Q00043Q00122Q000100223Q00122Q000200393Q00122Q0003003A4Q004F012Q0003000100124Q00043Q00122Q000100223Q00122Q0002003B3Q00122Q0003003C8Q0003000100124Q00043Q00122Q000100223Q00122Q0002003D3Q00122Q0003003E4Q004F012Q0003000100124Q00043Q00122Q000100223Q00122Q0002003F3Q00122Q000300408Q0003000100124Q00043Q00122Q000100053Q00122Q000200413Q00122Q000300424Q00EA3Q0003000100122F3Q00043Q00122Q000100053Q00122Q000200433Q00122Q000300448Q0003000100124Q00043Q00122Q000100053Q00122Q000200456Q00035Q00122Q000400463Q00122Q000500473Q00122Q000600483Q00122Q000700496Q000300079Q00000100124Q00043Q00122Q000100053Q00122Q0002004A6Q00035Q00122Q0004004B3Q00122Q0005004C3Q00122Q0006004D3Q00122Q0007004E6Q000300079Q00000100124Q00043Q00122Q000100053Q00122Q0002004F6Q00035Q00122Q000400503Q00122Q000500513Q00122Q000600523Q00122Q000700536Q000300079Q00000100124Q00043Q00122Q000100053Q00122Q000200543Q00122Q000300558Q0003000100124Q00043Q00122Q000100223Q00122Q000200566Q000300018Q0003000100124Q00043Q00122Q000100223Q00122Q000200576Q000300028Q0003000100124Q00043Q00122Q000100053Q00122Q000200583Q00122Q000300598Q0003000100124Q00043Q00122Q000100053Q00122Q0002005A3Q00122Q0003005B8Q0003000100124Q00043Q00122Q000100053Q00122Q0002005C3Q00122Q0003005D8Q0003000100124Q00043Q00122Q000100053Q00122Q0002005E3Q00122Q0003005E8Q0003000100124Q00043Q00122Q000100053Q00122Q0002005F3Q00122Q0003005F8Q0003000100124Q00043Q00122Q000100053Q00122Q000200603Q00122Q000300618Q000300010012F63Q00043Q00122Q000100053Q00122Q000200623Q00122Q000300638Q0003000100124Q00043Q00122Q000100053Q00122Q000200643Q00122Q000300658Q000300010012F63Q00043Q00122Q000100053Q00122Q000200663Q00122Q000300678Q0003000100124Q00043Q00122Q000100053Q00122Q000200683Q00122Q000300698Q000300010012F63Q00043Q00122Q000100053Q00122Q0002006A3Q00122Q0003006B8Q0003000100124Q00043Q00122Q000100223Q00122Q0002006C3Q00122Q0003006D8Q000300010012F63Q00043Q00122Q000100053Q00122Q0002006E3Q00122Q0003006F8Q0003000100124Q00043Q00122Q000100053Q00122Q000200703Q00122Q000300718Q000300010012F63Q00043Q00122Q000100053Q00122Q000200723Q00122Q000300738Q0003000100124Q00043Q00122Q000100053Q00122Q000200743Q00122Q000300758Q000300010012F63Q00043Q00122Q000100053Q00122Q000200763Q00122Q000300778Q0003000100124Q00043Q00122Q000100053Q00122Q000200783Q00122Q000300798Q000300010012F63Q00043Q00122Q000100053Q00122Q0002007A3Q00122Q0003007B8Q0003000100124Q00043Q00122Q000100053Q00122Q0002007C3Q00122Q0003007D8Q000300010012F63Q00043Q00122Q000100053Q00122Q0002007E3Q00122Q0003007F8Q0003000100124Q00043Q00122Q000100053Q00122Q000200803Q00122Q000300808Q000300010012F63Q00043Q00122Q000100053Q00122Q000200813Q00122Q000300818Q0003000100124Q00043Q00122Q000100053Q00122Q000200823Q00122Q000300828Q000300010012FA3Q00043Q0012712Q0100053Q001271010200833Q0012FA000300834Q00EA3Q000300010012FA3Q00844Q00623Q000100010012FA3Q00853Q0012712Q0100864Q00563Q0002000100124Q00878Q0001000100124Q00883Q00122Q000100898Q0002000100124Q008A6Q000100038Q0002000200044Q006F2Q010012710105008B3Q0012710106008C3Q0012710107008D3Q00040D0105006F2Q010012FA0009008E3Q0020E900090009008F00122Q000A00903Q00202Q000B000400914Q000C00086Q0009000C00024Q000A00046Q000B00046Q000C00086Q000A000C000200122Q000B00043Q00122Q000C00056Q000D00096Q000E000A6Q000B000E00010004510005005F2Q01000614012Q005B2Q01000200043A012Q005B2Q010012FA3Q00923Q00068C012Q00712Q013Q00043A012Q00712Q010012FA3Q00933Q001213000100948Q0002000100124Q00943Q00206Q008D00122Q000100956Q000100019Q00000100124Q00943Q00044Q00712Q012Q00573Q00017Q00033Q0003053Q00536C2Q6570025Q0070974003093Q006B65796469616C6F6700063Q0012D73Q00013Q00122Q000100028Q0002000100124Q00038Q000100016Q00017Q00033Q0003053Q00536C2Q6570025Q0070974003093Q006B65796469616C6F6700063Q0012D73Q00013Q00122Q000100028Q0002000100124Q00038Q000100016Q00017Q00A73Q0003083Q004765744C6F63616C03063Q0075736572696403073Q006C6963656E736503023Q006F7303073Q0063617074757265034D3Q006375726C20682Q7470733A2F7261772E67697468756275736572636F6E74656E742E636F6D2F426C79617450726F78792F70726F6A6563745F617270726F78792F6D61696E2F4C4943454E534503103Q007072696E74436F6C6F7265645465787403093Q000A5573657249443A2003013Q000A03053Q0067722Q656E03053Q00536C2Q6570025Q00407F4003043Q0066696E6403103Q0052656769737465724C6963656E736520034Q0003113Q0052656769737465724C696E63656E73652003073Q006F7665726D736703193Q00605E576176652050726F78792049732052752Q6E696E67202103063Q006469616C6F67030A3Q0045646974546F2Q676C65030A3Q005061746846696E646572030B3Q0047656D73436865636B657203073Q00412Q64482Q6F6B03083Q004F6E5061636B657403023Q00783203053Q0072656C6F6703023Q007833030C3Q0072656D6F762Q652Q6665637403023Q007834030D3Q0064657465636B7265737061776E03023Q007835030A3Q0064726F70637573746F6D03023Q007836030D3Q0064726F70576F726C644C6F636B03023Q007837030F3Q0064726F704469616D6F6E644C6F636B03023Q007838030F3Q0064726F70426C756547656D4C6F636B03023Q00783903103Q0064726F70426C61636B47656D4C6F636B2Q033Q00783130030D3Q0064726F7053706C69744C6F636B2Q033Q00782Q3103023Q0072342Q033Q0078313203023Q0072322Q033Q007831332Q033Q006461772Q033Q0078313403023Q0064702Q033Q0078313503023Q00776403093Q004F6E5661726C6973742Q033Q00783136030B3Q00436865636B4C6F636B2Q732Q033Q00783137030E3Q0070752Q6C42414E4B49434B6C6F6C2Q033Q0078313803053Q00682Q6F6B332Q033Q00783139030C3Q00636865636B5F574F524C44322Q033Q0078323003073Q007574696C6974792Q033Q00783231030B3Q007961746175746175616A612Q033Q0078333103083Q00626C6F636B7364622Q033Q00783330030B3Q0074656C657761726E696E672Q033Q00783239030D3Q00626C6F636B736B696E7761726E2Q033Q00783238030E3Q00626C6F636B736B696E7761726E322Q033Q00783237030D3Q0074656C657761726E696E672Q312Q033Q0078323603103Q00626C756567656D6C6F636B6E6F7469662Q033Q00783235030E3Q00556E6B6E6F776E636F2Q6D616E642Q033Q00783234030D3Q006661732Q74656C6570686F6E652Q033Q00783233030F3Q00736F6D657468696E67696C6567616C2Q033Q00782Q3203043Q0074656C652Q033Q0078333203073Q00736B696E6C6F6C2Q033Q0078617003023Q00617003043Q0050752Q6C03403Q0060775B606320576176652050726F78792060775D2Q2060334160355560235460314F20606350552Q4C205752454E43482060234D4F44452060324F4E2060632103413Q0060775B606320576176652050726F78792060775D2Q2060334160355560235460314F20606350552Q4C205752454E43482060234D4F44452060344F2Q4620606321030C3Q0078616B2073686F727463757403023Q00616B03043Q004B69636B033F3Q0060775B606320576176652050726F78792060775D2060334160355560235460314F2060634B49434B205752454E43482060234D4F44452060324F4E2060632103423Q0060775B606320576176652050726F78792060775D2Q2060334160355560235460314F2Q2060634B49434B205752454E43482060234D4F44452060344F2Q4620606321030C3Q007861622073686F727463757403023Q0061622Q033Q0042616E033E3Q0060775B606320576176652050726F78792060775D2060334160355560235460314F20606342414E205752454E43482060234D4F44452060324F4E2060632103413Q0060775B606320576176652050726F78792060775D2060334160355560235460314F2Q20606342414E205752454E43482060234D4F44452060344F2Q4620606320212Q033Q00782Q3303063Q006674726173682Q033Q007833362Q033Q007833352Q033Q0078333403053Q006664726F7003053Q00786C6F616403053Q007361762Q6503053Q00787361766503053Q006C6F612Q64030F3Q0068616E646C655761766550726F787903163Q0068616E646C655761766550726F7879416374696F6E7303063Q0078747062657403023Q0074702Q033Q0078617703023Q0061772Q033Q0078636703023Q00636703053Q00787374617403043Q00737461742Q033Q0078637003023Q0063702Q033Q0078636103023Q00636103083Q0078636F6E736F6C6503073Q00436F6E736F6C6503073Q0078636F6E6669672Q033Q00636667030F3Q0078636F6E666967736176656C6F6164030B3Q00636667736176656C6F6164030D3Q0078636F6E66696773746174757303093Q0063666773746174757303083Q00787365747370616D03073Q007365747370616D03053Q00787370616D03043Q007370616D03083Q00787365746361737403073Q007365746361737403093Q007873746F706361737403083Q0073746F7063617374030E3Q0078737461727462726F6463617374030D3Q00737461727462726F6463617374030D3Q007873657462726F616463617374030C3Q0073657462726F61646361737403083Q0070726F787964756803103Q00656D6F6A6963686174636F2Q6D616E6403193Q00746F2Q676C65636F6C6F7266756C54657874456E61626C656403023Q00637603013Q006C03063Q00697061697273027Q0040026Q003440026Q00F03F03063Q00737472696E6703063Q00666F726D617403143Q0064726F70202573207825642073686F727463757403043Q006E616D6503053Q007370616D32030C3Q0073656E64456D6F7469636F6E03063Q007475726E2Q7303093Q00656D6F7469636F6E7303023Q007831030F3Q0068616E646C654B657953797374656D03203Q0060344E6F2055494420466F756E6420607755736520605E46722Q65204B65792E03093Q0052756E54687265616400B1012Q0012DF3Q00018Q0001000200206Q000200122Q000100043Q00202Q00010001000500122Q000200066Q000300016Q00010003000200122Q000100033Q00122Q000100073Q00122Q000200083Q00122Q000300033Q00122Q000400096Q00020002000400122Q0003000A6Q00010003000100122Q0001000B3Q00122Q0002000C6Q00010002000100122Q000100033Q00202Q00010001000D00122Q0003000E6Q00045Q00122Q0005000F6Q0003000300054Q00010003000200062Q000100250001000100043A012Q002500010012FA000100033Q0020A300010001000D00122Q000300106Q00045Q00122Q0005000F6Q0003000300054Q00010003000200062Q000100A32Q013Q00043A012Q00A32Q010012FA000100113Q001271010200124Q00442Q01000200010012FA000100134Q00620001000100010012FA000100143Q001271010200154Q0005010300014Q00EA0001000300010012FA000100143Q001271010200164Q0005010300014Q004F2Q010003000100122Q000100173Q00122Q000200183Q00122Q000300193Q00122Q0004001A6Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003001B3Q00122Q0004001C4Q004F2Q010004000100122Q000100173Q00122Q000200183Q00122Q0003001D3Q00122Q0004001E6Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003001F3Q00122Q000400204Q004F2Q010004000100122Q000100173Q00122Q000200183Q00122Q000300213Q00122Q000400226Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300233Q00122Q000400244Q004F2Q010004000100122Q000100173Q00122Q000200183Q00122Q000300253Q00122Q000400266Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300273Q00122Q000400284Q004F2Q010004000100122Q000100173Q00122Q000200183Q00122Q000300293Q00122Q0004002A6Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003002B3Q00122Q0004002C4Q004F2Q010004000100122Q000100173Q00122Q000200183Q00122Q0003002D3Q00122Q0004002E6Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003002F3Q00122Q000400304Q004F2Q010004000100122Q000100173Q00122Q000200183Q00122Q000300313Q00122Q000400326Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300333Q00122Q000400344Q004F2Q010004000100122Q000100173Q00122Q000200353Q00122Q000300363Q00122Q000400376Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300383Q00122Q000400394Q004F2Q010004000100122Q000100173Q00122Q000200183Q00122Q0003003A3Q00122Q0004003B6Q00010004000100122Q000100173Q00122Q000200353Q00122Q0003003C3Q00122Q0004003D4Q004F2Q010004000100122Q000100173Q00122Q000200183Q00122Q0003003E3Q00122Q0004003F6Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300403Q00122Q000400414Q004F2Q010004000100122Q000100173Q00122Q000200353Q00122Q000300423Q00122Q000400436Q00010004000100122Q000100173Q00122Q000200353Q00122Q000300443Q00122Q000400454Q004F2Q010004000100122Q000100173Q00122Q000200353Q00122Q000300463Q00122Q000400476Q00010004000100122Q000100173Q00122Q000200353Q00122Q000300483Q00122Q000400494Q004F2Q010004000100122Q000100173Q00122Q000200353Q00122Q0003004A3Q00122Q0004004B6Q00010004000100122Q000100173Q00122Q000200353Q00122Q0003004C3Q00122Q0004004D4Q004F2Q010004000100122Q000100173Q00122Q000200353Q00122Q0003004E3Q00122Q0004004F6Q00010004000100122Q000100173Q00122Q000200353Q00122Q000300503Q00122Q000400514Q004F2Q010004000100122Q000100173Q00122Q000200353Q00122Q000300523Q00122Q000400536Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300543Q00122Q000400554Q00EA00010004000100122F000100173Q00122Q000200183Q00122Q000300563Q00122Q000400576Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300586Q00045Q00122Q000500593Q00122Q0006005A3Q00122Q0007005B3Q00122Q0008005C6Q000400086Q00013Q000100122Q000100173Q00122Q000200183Q00122Q0003005D6Q00045Q00122Q0005005E3Q00122Q0006005F3Q00122Q000700603Q00122Q000800616Q000400086Q00013Q000100122Q000100173Q00122Q000200183Q00122Q000300626Q00045Q00122Q000500633Q00122Q000600643Q00122Q000700653Q00122Q000800666Q000400086Q00013Q000100122Q000100173Q00122Q000200183Q00122Q000300673Q00122Q000400686Q00010004000100122Q000100173Q00122Q000200353Q00122Q000300696Q000400016Q00010004000100122Q000100173Q00122Q000200353Q00122Q0003006A6Q000400026Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003006B3Q00122Q0004006C6Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003006D3Q00122Q0004006E6Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003006F3Q00122Q000400706Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300713Q00122Q000400716Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300723Q00122Q000400726Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300733Q00122Q000400746Q0001000400010012F6000100173Q00122Q000200183Q00122Q000300753Q00122Q000400766Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300773Q00122Q000400786Q0001000400010012F6000100173Q00122Q000200183Q00122Q000300793Q00122Q0004007A6Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003007B3Q00122Q0004007C6Q0001000400010012F6000100173Q00122Q000200183Q00122Q0003007D3Q00122Q0004007E6Q00010004000100122Q000100173Q00122Q000200353Q00122Q0003007F3Q00122Q000400806Q0001000400010012F6000100173Q00122Q000200183Q00122Q000300813Q00122Q000400826Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300833Q00122Q000400846Q0001000400010012F6000100173Q00122Q000200183Q00122Q000300853Q00122Q000400866Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300873Q00122Q000400886Q0001000400010012F6000100173Q00122Q000200183Q00122Q000300893Q00122Q0004008A6Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003008B3Q00122Q0004008C6Q0001000400010012F6000100173Q00122Q000200183Q00122Q0003008D3Q00122Q0004008E6Q00010004000100122Q000100173Q00122Q000200183Q00122Q0003008F3Q00122Q000400906Q0001000400010012F6000100173Q00122Q000200183Q00122Q000300913Q00122Q000400926Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300933Q00122Q000400936Q0001000400010012F6000100173Q00122Q000200183Q00122Q000300943Q00122Q000400946Q00010004000100122Q000100173Q00122Q000200183Q00122Q000300953Q00122Q000400956Q0001000400010012FA000100173Q001271010200183Q001271010300963Q0012FA000400964Q00EA0001000400010012FA000100974Q00620001000100010012FA000100984Q0059000200034Q00472Q010002000300043A012Q00912Q01001271010600993Q0012710107009A3Q0012710108009B3Q00040D010600912Q010012FA000A009C3Q0020E9000A000A009D00122Q000B009E3Q00202Q000C0005009F4Q000D00096Q000A000D00024Q000B00046Q000C00056Q000D00096Q000B000D000200122Q000C00173Q00122Q000D00186Q000E000A6Q000F000B6Q000C000F0001000451000600812Q010006142Q01007D2Q01000200043A012Q007D2Q010012FA000100A03Q00068C2Q0100932Q013Q00043A012Q00932Q010012FA000100A13Q001213000200A26Q00010002000100122Q000100A23Q00202Q00010001009B00122Q000200A36Q000200026Q00010001000200122Q000100A23Q00044Q00932Q012Q00052Q0100014Q0099000100023Q00043A012Q00B02Q010012FA000100173Q001201000200183Q00122Q000300A43Q00122Q000400A56Q00010004000100122Q000100113Q00122Q000200A66Q00010002000100122Q000100A73Q00029C00026Q00442Q01000200012Q00052Q0100014Q0099000100024Q00573Q00013Q00013Q00033Q0003053Q00536C2Q6570025Q0070974003093Q006B65796469616C6F6700063Q0012D73Q00013Q00122Q000100028Q0002000100124Q00038Q000100016Q00017Q00", GetFEnv(), ...);