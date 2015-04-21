// This object will hold all exports.
var Haste = {};

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

function F(f) {
    this.f = f;
}

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Apply
   Applies the function f to the arguments args. If the application is under-
   saturated, a closure is returned, awaiting further arguments. If it is over-
   saturated, the function is fully applied, and the result (assumed to be a
   function) is then applied to the remaining arguments.
*/
function A(f, args) {
    if(f instanceof T) {
        f = E(f);
    }
    // Closure does some funny stuff with functions that occasionally
    // results in non-functions getting applied, so we have to deal with
    // it.
    if(!(f instanceof Function)) {
        f = B(f);
        if(!(f instanceof Function)) {
            return f;
        }
    }

    if(f.arity === undefined) {
        f.arity = f.length;
    }
    if(args.length === f.arity) {
        switch(f.arity) {
            case 0:  return f();
            case 1:  return f(args[0]);
            default: return f.apply(null, args);
        }
    } else if(args.length > f.arity) {
        switch(f.arity) {
            case 0:  return f();
            case 1:  return A(f(args.shift()), args);
            default: return A(f.apply(null, args.splice(0, f.arity)), args);
        }
    } else {
        var g = function() {
            return A(f, args.concat(Array.prototype.slice.call(arguments)));
        };
        g.arity = f.arity - args.length;
        return g;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            var f = t.f;
            t.f = __blackhole;
            if(t.x === __updatable) {
                t.x = f();
            } else {
                return f();
            }
        }
        return t.x;
    } else {
        return t;
    }
}

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        f = fun();
    }
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw err;
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return [0, (a-a%b)/b, a%b];
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return [0, sign, manHigh, manLow, exp];
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, [0]);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [[0, str.charCodeAt(i)], acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,[0,str.charCodeAt(i)],new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1])[1]);
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x[1];
    return x[2];
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return [0];
    } else if(a == b) {
        return [1];
    }
    return [2];
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function jsAlert(val) {
    if(typeof alert != 'undefined') {
        alert(val);
    } else {
        print(val);
    }
}

function jsLog(val) {
    console.log(val);
}

function jsPrompt(str) {
    var val;
    if(typeof prompt != 'undefined') {
        val = prompt(str);
    } else {
        print(str);
        val = readline();
    }
    return val == undefined ? '' : val.toString();
}

function jsEval(str) {
    var x = eval(str);
    return x == undefined ? '' : x.toString();
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

function jsSetCB(elem, evt, cb) {
    // Count return press in single line text box as a change event.
    if(evt == 'change' && elem.type.toLowerCase() == 'text') {
        setCB(elem, 'keyup', function(k) {
            if(k == '\n'.charCodeAt(0)) {
                B(A(cb,[[0,k.keyCode],0]));
            }
        });
    }

    var fun;
    switch(evt) {
    case 'click':
    case 'dblclick':
    case 'mouseup':
    case 'mousedown':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            B(A(cb,[[0,x.button],[0,mx,my],0]));
        };
        break;
    case 'mousemove':
    case 'mouseover':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            B(A(cb,[[0,mx,my],0]));
        };
        break;
    case 'keypress':
    case 'keyup':
    case 'keydown':
        fun = function(x) {B(A(cb,[[0,x.keyCode],0]));};
        break;
    case 'wheel':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            var mdx = [0,x.deltaX];
            var mdy = [0,x.deltaY];
            var mdz = [0,x.deltaZ];
            B(A(cb,[[0,mx,my],[0,mdx,mdy,mdz],0]));
        };
        break;
    default:
        fun = function() {B(A(cb,[0]));};
        break;
    }
    return setCB(elem, evt, fun);
}

function setCB(elem, evt, cb) {
    if(elem.addEventListener) {
        elem.addEventListener(evt, cb, false);
        return true;
    } else if(elem.attachEvent) {
        elem.attachEvent('on'+evt, cb);
        return true;
    }
    return false;
}

function jsSetTimeout(msecs, cb) {
    window.setTimeout(function() {B(A(cb,[0]));}, msecs);
}

function jsGet(elem, prop) {
    return elem[prop].toString();
}

function jsSet(elem, prop, val) {
    elem[prop] = val;
}

function jsGetAttr(elem, prop) {
    if(elem.hasAttribute(prop)) {
        return elem.getAttribute(prop).toString();
    } else {
        return "";
    }
}

function jsSetAttr(elem, prop, val) {
    elem.setAttribute(prop, val);
}

function jsGetStyle(elem, prop) {
    return elem.style[prop].toString();
}

function jsSetStyle(elem, prop, val) {
    elem.style[prop] = val;
}

function jsKillChild(child, parent) {
    parent.removeChild(child);
}

function jsClearChildren(elem) {
    while(elem.hasChildNodes()){
        elem.removeChild(elem.lastChild);
    }
}

function jsFind(elem) {
    var e = document.getElementById(elem)
    if(e) {
        return [1,[0,e]];
    }
    return [0];
}

function jsElemsByClassName(cls) {
    var es = document.getElementsByClassName(cls);
    var els = [0];

    for (var i = es.length-1; i >= 0; --i) {
        els = [1, [0, es[i]], els];
    }
    return els;
}

function jsQuerySelectorAll(elem, query) {
    var els = [0], nl;

    if (!elem || typeof elem.querySelectorAll !== 'function') {
        return els;
    }

    nl = elem.querySelectorAll(query);

    for (var i = nl.length-1; i >= 0; --i) {
        els = [1, [0, nl[i]], els];
    }

    return els;
}

function jsCreateElem(tag) {
    return document.createElement(tag);
}

function jsCreateTextNode(str) {
    return document.createTextNode(str);
}

function jsGetChildBefore(elem) {
    elem = elem.previousSibling;
    while(elem) {
        if(typeof elem.tagName != 'undefined') {
            return [1,[0,elem]];
        }
        elem = elem.previousSibling;
    }
    return [0];
}

function jsGetLastChild(elem) {
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,[0,elem.childNodes[i]]];
        }
    }
    return [0];
}


function jsGetFirstChild(elem) {
    var len = elem.childNodes.length;
    for(var i = 0; i < len; i++) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,[0,elem.childNodes[i]]];
        }
    }
    return [0];
}


function jsGetChildren(elem) {
    var children = [0];
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            children = [1, [0,elem.childNodes[i]], children];
        }
    }
    return children;
}

function jsSetChildren(elem, children) {
    children = E(children);
    jsClearChildren(elem, 0);
    while(children[0] === 1) {
        elem.appendChild(E(E(children[1])[1]));
        children = E(children[2]);
    }
}

function jsAppendChild(child, container) {
    container.appendChild(child);
}

function jsAddChildBefore(child, container, after) {
    container.insertBefore(child, after);
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1])[1]);
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

var jsJSONParse = JSON.parse;

// JSON stringify a string
function jsStringify(str) {
    return JSON.stringify(str);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, jsRead(obj)];
    case 'string':
        return [1, obj];
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst_json(obj, 0)];
        } else if (obj == null) {
            return [5];
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = [1, [0, [0,ks[i]], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst_json(arr,elem+1);}),true]
}

function arr2lst(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, arr[elem], new T(function() {return arr2lst(arr,elem+1);})]
}
window['arr2lst'] = arr2lst;

function lst2arr(xs) {
    var arr = [];
    for(; xs[0]; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}
window['lst2arr'] = lst2arr;

function ajaxReq(method, url, async, postdata, cb) {
    var xhr = new XMLHttpRequest();
    xhr.open(method, url, async);

    if(method == "POST") {
        xhr.setRequestHeader("Content-type",
                             "application/x-www-form-urlencoded");
    }
    xhr.onreadystatechange = function() {
        if(xhr.readyState == 4) {
            if(xhr.status == 200) {
                B(A(cb,[[1,[0,xhr.responseText]],0]));
            } else {
                B(A(cb,[[0],0])); // Nothing
            }
        }
    }
    xhr.send(postdata);
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;

function makeStableName(x) {
    if(!x.stableName) {
        x.stableName = __next_stable_name;
        __next_stable_name += 1;
    }
    return x.stableName;
}

function eqStableName(x, y) {
    return (x == y) ? 1 : 0;
}

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

var I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

var I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 + b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 + b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 + b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 + b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 * b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 * b00;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c16 += a00 * b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 * b00;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a16 * b16;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a00 * b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

// Joseph Myers' MD5 implementation; used under the BSD license.

function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s) {
    var n = s.length,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=s.length; i+=64) {
        md5cycle(state, md5blk(s.substring(i-64, i)));
    }
    s = s.substring(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<s.length; i++)
        tail[i>>2] |= s.charCodeAt(i) << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s.charCodeAt(i)
            + (s.charCodeAt(i+1) << 8)
            + (s.charCodeAt(i+2) << 16)
            + (s.charCodeAt(i+3) << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s) {
    return hex(md51(s));
}

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = [];
    for(; n >= 0; --n) {
        arr.push(x);
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// 2D Canvas drawing primitives.
function jsHasCtx2D(elem) {return !!elem.getContext;}
function jsGetCtx2D(elem) {return elem.getContext('2d');}
function jsBeginPath(ctx) {ctx.beginPath();}
function jsMoveTo(ctx, x, y) {ctx.moveTo(x, y);}
function jsLineTo(ctx, x, y) {ctx.lineTo(x, y);}
function jsStroke(ctx) {ctx.stroke();}
function jsFill(ctx) {ctx.fill();}
function jsRotate(ctx, radians) {ctx.rotate(radians);}
function jsTranslate(ctx, x, y) {ctx.translate(x, y);}
function jsScale(ctx, x, y) {ctx.scale(x, y);}
function jsPushState(ctx) {ctx.save();}
function jsPopState(ctx) {ctx.restore();}
function jsResetCanvas(el) {el.width = el.width;}
function jsDrawImage(ctx, img, x, y) {ctx.drawImage(img, x, y);}
function jsDrawImageClipped(ctx, img, x, y, cx, cy, cw, ch) {
    ctx.drawImage(img, cx, cy, cw, ch, x, y, cw, ch);
}
function jsDrawText(ctx, str, x, y) {ctx.fillText(str, x, y);}
function jsClip(ctx) {ctx.clip();}
function jsArc(ctx, x, y, radius, fromAngle, toAngle) {
    ctx.arc(x, y, radius, fromAngle, toAngle);
}
function jsCanvasToDataURL(el) {return el.toDataURL('image/png');}

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return [0, 1, E(w).val];
}

function finalizeWeak(w) {
    return [0, B(A(E(w).fin, [0]))];
}

var _0=new T(function(){return B(unCStr("Prelude.undefined"));}),_1=new T(function(){return B(err(_0));}),_2=function(_3,_4){return E(_1);},_5=new T(function(){return B(unCStr(" \u2194 "));}),_6=new T(function(){return B(unCStr(" \u2192 "));}),_7=new T(function(){return B(unCStr(" \u2228 "));}),_8=[0,41],_9=[0],_a=[1,_8,_9],_b=new T(function(){return B(unCStr(" \u2227 "));}),_c=[0,40],_d=[0,172],_e=function(_f,_g){var _h=E(_f);return _h[0]==0?E(_g):[1,_h[1],new T(function(){return B(_e(_h[2],_g));})];},_i=function(_j,_k){switch(E(_j)[0]){case 0:var _l=E(_k);return _l[0]==0?E(_1):E(_l[2])[0]==0?[0,_d,_l[1]]:E(_1);case 1:var _m=E(_k);if(!_m[0]){return E(_1);}else{var _n=E(_m[2]);return _n[0]==0?E(_1):E(_n[2])[0]==0?[0,_c,new T(function(){return B(_e(_m[1],new T(function(){return B(_e(_b,new T(function(){return B(_e(_n[1],_a));},1)));},1)));})]:E(_1);}break;case 2:var _o=E(_k);if(!_o[0]){return E(_1);}else{var _p=E(_o[2]);return _p[0]==0?E(_1):E(_p[2])[0]==0?[0,_c,new T(function(){return B(_e(_o[1],new T(function(){return B(_e(_7,new T(function(){return B(_e(_p[1],_a));},1)));},1)));})]:E(_1);}break;case 3:var _q=E(_k);if(!_q[0]){return E(_1);}else{var _r=E(_q[2]);return _r[0]==0?E(_1):E(_r[2])[0]==0?[0,_c,new T(function(){return B(_e(_q[1],new T(function(){return B(_e(_6,new T(function(){return B(_e(_r[1],_a));},1)));},1)));})]:E(_1);}break;default:var _s=E(_k);if(!_s[0]){return E(_1);}else{var _t=E(_s[2]);return _t[0]==0?E(_1):E(_t[2])[0]==0?[0,_c,new T(function(){return B(_e(_s[1],new T(function(){return B(_e(_5,new T(function(){return B(_e(_t[1],_a));},1)));},1)));})]:E(_1);}}},_u=function(_v,_w){var _x=B(_i(_v,_w));return [1,_x[1],_x[2]];},_y=function(_z,_A){var _B=jsShowI(_z),_C=_B;return new F(function(){return _e(fromJSStr(_C),_A);});},_D=[0,41],_E=[0,40],_F=function(_G,_H,_I){if(_H>=0){return new F(function(){return _y(_H,_I);});}else{return _G<=6?B(_y(_H,_I)):[1,_E,new T(function(){var _J=jsShowI(_H),_K=_J;return B(_e(fromJSStr(_K),[1,_D,_I]));})];}},_L=function(_M){return new F(function(){return unAppCStr("P_",new T(function(){return B(_F(0,E(E(_M)[2])[1],_9));}));});},_N=function(_O,_P){return new F(function(){return _L(_O);});},_Q=function(_R){return E(_1);},_S=[0,_],_T=function(_U){return [1,_,_U];},_V=[0,_],_W=function(_X){return [1,_,_X];},_Y=function(_Z){var _10=E(_Z);switch(_10[0]){case 0:return E(_V);case 1:return new F(function(){return _W(_10[1]);});break;case 2:return [3,_,_10[1],new T(function(){return B(_Y(_10[2]));})];default:return [5,_,_10[1],new T(function(){return B(_Y(_10[2]));}),new T(function(){return B(_Y(_10[3]));})];}},_11=function(_12){var _13=E(_12);switch(_13[0]){case 0:return E(_S);case 1:return new F(function(){return _T(_13[1]);});break;case 2:return [3,_,_13[1],new T(function(){return B(_Y(_13[2]));})];case 3:return [5,_,_13[1],new T(function(){return B(_Y(_13[2]));}),new T(function(){return B(_Y(_13[3]));})];case 4:return [7,_,_13[1],new T(function(){return B(_11(_13[2]));})];case 5:return [9,_,_13[1],new T(function(){return B(_11(_13[2]));}),new T(function(){return B(_11(_13[3]));})];default:return [11,_,_13[1],function(_14){return new F(function(){return _11(B(A(_13[2],[_14])));});}];}},_15=function(_16){return E(_1);},_17=function(_18,_19){switch(E(_18)[0]){case 0:return E(_19)[0]==0?true:false;case 1:return E(_19)[0]==1?true:false;case 2:return E(_19)[0]==2?true:false;case 3:return E(_19)[0]==3?true:false;default:return E(_19)[0]==4?true:false;}},_1a=function(_1b,_1c){return E(_1b)[1]==E(_1c)[1];},_1d=function(_1e,_1f){return new F(function(){return _1a(E(_1e)[2],E(_1f)[2]);});},_1g=function(_1h,_1i){return E(_1);},_1j=function(_1k,_1l,_){var _1m=jsGet(_1k,toJSStr(E(_1l))),_1n=_1m;return new T(function(){return fromJSStr(_1n);});},_1o=[3,_],_1p=[13,_],_1q=new T(function(){return B(unCStr("wheel"));}),_1r=new T(function(){return B(unCStr("mouseout"));}),_1s=new T(function(){return B(unCStr("mouseover"));}),_1t=new T(function(){return B(unCStr("mousemove"));}),_1u=new T(function(){return B(unCStr("blur"));}),_1v=new T(function(){return B(unCStr("focus"));}),_1w=new T(function(){return B(unCStr("change"));}),_1x=new T(function(){return B(unCStr("unload"));}),_1y=new T(function(){return B(unCStr("load"));}),_1z=new T(function(){return B(unCStr("submit"));}),_1A=new T(function(){return B(unCStr("keydown"));}),_1B=new T(function(){return B(unCStr("keyup"));}),_1C=new T(function(){return B(unCStr("keypress"));}),_1D=new T(function(){return B(unCStr("mouseup"));}),_1E=new T(function(){return B(unCStr("mousedown"));}),_1F=new T(function(){return B(unCStr("dblclick"));}),_1G=new T(function(){return B(unCStr("click"));}),_1H=function(_1I){switch(E(_1I)[0]){case 0:return E(_1y);case 1:return E(_1x);case 2:return E(_1w);case 3:return E(_1v);case 4:return E(_1u);case 5:return E(_1t);case 6:return E(_1s);case 7:return E(_1r);case 8:return E(_1G);case 9:return E(_1F);case 10:return E(_1E);case 11:return E(_1D);case 12:return E(_1C);case 13:return E(_1B);case 14:return E(_1A);case 15:return E(_1z);default:return E(_1q);}},_1J=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_1K=new T(function(){return B(unCStr("main"));}),_1L=new T(function(){return B(unCStr("EventData"));}),_1M=new T(function(){var _1N=hs_wordToWord64(3703396926),_1O=_1N,_1P=hs_wordToWord64(1660403598),_1Q=_1P;return [0,_1O,_1Q,[0,_1O,_1Q,_1K,_1J,_1L],_9];}),_1R=[0,0],_1S=false,_1T=2,_1U=[1],_1V=new T(function(){return B(unCStr("Dynamic"));}),_1W=new T(function(){return B(unCStr("Data.Dynamic"));}),_1X=new T(function(){return B(unCStr("base"));}),_1Y=new T(function(){var _1Z=hs_wordToWord64(628307645),_20=_1Z,_21=hs_wordToWord64(949574464),_22=_21;return [0,_20,_22,[0,_20,_22,_1X,_1W,_1V],_9];}),_23=[0],_24=new T(function(){return B(unCStr("OnLoad"));}),_25=[0,_24,_23],_26=[0,_1M,_25],_27=[0,_1Y,_26],_28=[0],_29=function(_){return _28;},_2a=function(_2b,_){return _28;},_2c=[0,_29,_2a],_2d=[0,_9,_1R,_1T,_2c,_1S,_27,_1U],_2e=function(_){var _=0,_2f=newMVar(),_2g=_2f,_=putMVar(_2g,_2d);return [0,_2g];},_2h=function(_2i){var _2j=B(A(_2i,[_])),_2k=_2j;return E(_2k);},_2l=new T(function(){return B(_2h(_2e));}),_2m=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2n=new T(function(){return B(unCStr("base"));}),_2o=new T(function(){return B(unCStr("PatternMatchFail"));}),_2p=new T(function(){var _2q=hs_wordToWord64(18445595),_2r=_2q,_2s=hs_wordToWord64(52003073),_2t=_2s;return [0,_2r,_2t,[0,_2r,_2t,_2n,_2m,_2o],_9];}),_2u=function(_2v){return E(_2p);},_2w=function(_2x){return E(E(_2x)[1]);},_2y=function(_2z,_2A,_2B){var _2C=B(A(_2z,[_])),_2D=B(A(_2A,[_])),_2E=hs_eqWord64(_2C[1],_2D[1]),_2F=_2E;if(!E(_2F)){return [0];}else{var _2G=hs_eqWord64(_2C[2],_2D[2]),_2H=_2G;return E(_2H)==0?[0]:[1,_2B];}},_2I=function(_2J){var _2K=E(_2J);return new F(function(){return _2y(B(_2w(_2K[1])),_2u,_2K[2]);});},_2L=function(_2M){return E(E(_2M)[1]);},_2N=function(_2O,_2P){return new F(function(){return _e(E(_2O)[1],_2P);});},_2Q=[0,44],_2R=[0,93],_2S=[0,91],_2T=function(_2U,_2V,_2W){var _2X=E(_2V);return _2X[0]==0?B(unAppCStr("[]",_2W)):[1,_2S,new T(function(){return B(A(_2U,[_2X[1],new T(function(){var _2Y=function(_2Z){var _30=E(_2Z);return _30[0]==0?E([1,_2R,_2W]):[1,_2Q,new T(function(){return B(A(_2U,[_30[1],new T(function(){return B(_2Y(_30[2]));})]));})];};return B(_2Y(_2X[2]));})]));})];},_31=function(_32,_33){return new F(function(){return _2T(_2N,_32,_33);});},_34=function(_35,_36,_37){return new F(function(){return _e(E(_36)[1],_37);});},_38=[0,_34,_2L,_31],_39=new T(function(){return [0,_2u,_38,_3a,_2I];}),_3a=function(_3b){return [0,_39,_3b];},_3c=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3d=function(_3e,_3f){return new F(function(){return die(new T(function(){return B(A(_3f,[_3e]));}));});},_3g=function(_3h,_3i){var _3j=E(_3i);if(!_3j[0]){return [0,_9,_9];}else{var _3k=_3j[1];if(!B(A(_3h,[_3k]))){return [0,_9,_3j];}else{var _3l=new T(function(){var _3m=B(_3g(_3h,_3j[2]));return [0,_3m[1],_3m[2]];});return [0,[1,_3k,new T(function(){return E(E(_3l)[1]);})],new T(function(){return E(E(_3l)[2]);})];}}},_3n=[0,32],_3o=[0,10],_3p=[1,_3o,_9],_3q=function(_3r){return E(E(_3r)[1])==124?false:true;},_3s=function(_3t,_3u){var _3v=B(_3g(_3q,B(unCStr(_3t)))),_3w=_3v[1],_3x=function(_3y,_3z){return new F(function(){return _e(_3y,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_e(_3u,new T(function(){return B(_e(_3z,_3p));},1)));})));},1));});},_3A=E(_3v[2]);if(!_3A[0]){return new F(function(){return _3x(_3w,_9);});}else{return E(E(_3A[1])[1])==124?B(_3x(_3w,[1,_3n,_3A[2]])):B(_3x(_3w,_9));}},_3B=function(_3C){return new F(function(){return _3d([0,new T(function(){return B(_3s(_3C,_3c));})],_3a);});},_3D=new T(function(){return B(_3B("Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_3E=[0,_1y,_23],_3F=[0,_1M,_3E],_3G=[0,_1x,_23],_3H=[0,_1M,_3G],_3I=[0,_1w,_23],_3J=[0,_1M,_3I],_3K=[0,_1v,_23],_3L=[0,_1M,_3K],_3M=[0,_1u,_23],_3N=[0,_1M,_3M],_3O=[3],_3P=[0,_1r,_3O],_3Q=[0,_1M,_3P],_3R=function(_3S,_3T){switch(E(_3S)[0]){case 0:return function(_){var _3U=E(_2l)[1],_3V=takeMVar(_3U),_3W=_3V,_=putMVar(_3U,new T(function(){var _3X=E(_3W);return [0,_3X[1],_3X[2],_3X[3],_3X[4],_3X[5],_3F,_3X[7]];}));return new F(function(){return A(_3T,[_]);});};case 1:return function(_){var _3Y=E(_2l)[1],_3Z=takeMVar(_3Y),_40=_3Z,_=putMVar(_3Y,new T(function(){var _41=E(_40);return [0,_41[1],_41[2],_41[3],_41[4],_41[5],_3H,_41[7]];}));return new F(function(){return A(_3T,[_]);});};case 2:return function(_){var _42=E(_2l)[1],_43=takeMVar(_42),_44=_43,_=putMVar(_42,new T(function(){var _45=E(_44);return [0,_45[1],_45[2],_45[3],_45[4],_45[5],_3J,_45[7]];}));return new F(function(){return A(_3T,[_]);});};case 3:return function(_){var _46=E(_2l)[1],_47=takeMVar(_46),_48=_47,_=putMVar(_46,new T(function(){var _49=E(_48);return [0,_49[1],_49[2],_49[3],_49[4],_49[5],_3L,_49[7]];}));return new F(function(){return A(_3T,[_]);});};case 4:return function(_){var _4a=E(_2l)[1],_4b=takeMVar(_4a),_4c=_4b,_=putMVar(_4a,new T(function(){var _4d=E(_4c);return [0,_4d[1],_4d[2],_4d[3],_4d[4],_4d[5],_3N,_4d[7]];}));return new F(function(){return A(_3T,[_]);});};case 5:return function(_4e){return function(_){var _4f=E(_2l)[1],_4g=takeMVar(_4f),_4h=_4g,_=putMVar(_4f,new T(function(){var _4i=E(_4h);return [0,_4i[1],_4i[2],_4i[3],_4i[4],_4i[5],[0,_1M,[0,_1t,[2,E(_4e)]]],_4i[7]];}));return new F(function(){return A(_3T,[_]);});};};case 6:return function(_4j){return function(_){var _4k=E(_2l)[1],_4l=takeMVar(_4k),_4m=_4l,_=putMVar(_4k,new T(function(){var _4n=E(_4m);return [0,_4n[1],_4n[2],_4n[3],_4n[4],_4n[5],[0,_1M,[0,_1s,[2,E(_4j)]]],_4n[7]];}));return new F(function(){return A(_3T,[_]);});};};case 7:return function(_){var _4o=E(_2l)[1],_4p=takeMVar(_4o),_4q=_4p,_=putMVar(_4o,new T(function(){var _4r=E(_4q);return [0,_4r[1],_4r[2],_4r[3],_4r[4],_4r[5],_3Q,_4r[7]];}));return new F(function(){return A(_3T,[_]);});};case 8:return function(_4s,_4t){return function(_){var _4u=E(_2l)[1],_4v=takeMVar(_4u),_4w=_4v,_=putMVar(_4u,new T(function(){var _4x=E(_4w);return [0,_4x[1],_4x[2],_4x[3],_4x[4],_4x[5],[0,_1M,[0,_1G,[1,_4s,E(_4t)]]],_4x[7]];}));return new F(function(){return A(_3T,[_]);});};};case 9:return function(_4y,_4z){return function(_){var _4A=E(_2l)[1],_4B=takeMVar(_4A),_4C=_4B,_=putMVar(_4A,new T(function(){var _4D=E(_4C);return [0,_4D[1],_4D[2],_4D[3],_4D[4],_4D[5],[0,_1M,[0,_1F,[1,_4y,E(_4z)]]],_4D[7]];}));return new F(function(){return A(_3T,[_]);});};};case 10:return function(_4E,_4F){return function(_){var _4G=E(_2l)[1],_4H=takeMVar(_4G),_4I=_4H,_=putMVar(_4G,new T(function(){var _4J=E(_4I);return [0,_4J[1],_4J[2],_4J[3],_4J[4],_4J[5],[0,_1M,[0,_1E,[1,_4E,E(_4F)]]],_4J[7]];}));return new F(function(){return A(_3T,[_]);});};};case 11:return function(_4K,_4L){return function(_){var _4M=E(_2l)[1],_4N=takeMVar(_4M),_4O=_4N,_=putMVar(_4M,new T(function(){var _4P=E(_4O);return [0,_4P[1],_4P[2],_4P[3],_4P[4],_4P[5],[0,_1M,[0,_1D,[1,_4K,E(_4L)]]],_4P[7]];}));return new F(function(){return A(_3T,[_]);});};};case 12:return function(_4Q,_){var _4R=E(_2l)[1],_4S=takeMVar(_4R),_4T=_4S,_=putMVar(_4R,new T(function(){var _4U=E(_4T);return [0,_4U[1],_4U[2],_4U[3],_4U[4],_4U[5],[0,_1M,[0,_1C,[4,_4Q]]],_4U[7]];}));return new F(function(){return A(_3T,[_]);});};case 13:return function(_4V,_){var _4W=E(_2l)[1],_4X=takeMVar(_4W),_4Y=_4X,_=putMVar(_4W,new T(function(){var _4Z=E(_4Y);return [0,_4Z[1],_4Z[2],_4Z[3],_4Z[4],_4Z[5],[0,_1M,[0,_1B,[4,_4V]]],_4Z[7]];}));return new F(function(){return A(_3T,[_]);});};case 14:return function(_50,_){var _51=E(_2l)[1],_52=takeMVar(_51),_53=_52,_=putMVar(_51,new T(function(){var _54=E(_53);return [0,_54[1],_54[2],_54[3],_54[4],_54[5],[0,_1M,[0,_1A,[4,_50]]],_54[7]];}));return new F(function(){return A(_3T,[_]);});};default:return E(_3D);}},_55=[0,_1H,_3R],_56=function(_57,_58,_){var _59=jsCreateTextNode(toJSStr(E(_57))),_5a=_59,_5b=jsAppendChild(_5a,E(_58)[1]);return [0,_5a];},_5c=0,_5d=function(_5e,_5f,_5g,_5h){return new F(function(){return A(_5e,[function(_){var _5i=jsSetAttr(E(_5f)[1],toJSStr(E(_5g)),toJSStr(E(_5h)));return _5c;}]);});},_5j=[0,112],_5k=function(_5l){var _5m=new T(function(){return E(E(_5l)[2]);});return function(_5n,_){return [0,[1,_5j,new T(function(){return B(_e(B(_F(0,E(_5m)[1],_9)),new T(function(){return E(E(_5l)[1]);},1)));})],new T(function(){var _5o=E(_5l);return [0,_5o[1],new T(function(){return [0,E(_5m)[1]+1|0];}),_5o[3],_5o[4],_5o[5],_5o[6],_5o[7]];})];};},_5p=new T(function(){return B(unCStr("id"));}),_5q=function(_5r){return E(_5r);},_5s=new T(function(){return B(unCStr("noid"));}),_5t=function(_5u,_){return _5u;},_5v=function(_5w,_5x,_){var _5y=jsFind(toJSStr(E(_5x))),_5z=_5y,_5A=E(_5z);if(!_5A[0]){var _5B=E(_2l)[1],_5C=takeMVar(_5B),_5D=_5C,_5E=B(A(_5w,[_5D,_])),_5F=_5E,_5G=E(_5F),_=putMVar(_5B,_5G[2]);return E(_5G[1])[2];}else{var _5H=E(_5A[1]),_5I=jsClearChildren(_5H[1]),_5J=E(_2l)[1],_5K=takeMVar(_5J),_5L=_5K,_5M=B(A(_5w,[_5L,_])),_5N=_5M,_5O=E(_5N),_5P=E(_5O[1]),_=putMVar(_5J,_5O[2]),_5Q=B(A(_5P[1],[_5H,_])),_5R=_5Q;return _5P[2];}},_5S=new T(function(){return B(unCStr("span"));}),_5T=function(_5U,_5V,_5W,_){var _5X=jsCreateElem(toJSStr(E(_5S))),_5Y=_5X,_5Z=jsAppendChild(_5Y,E(_5W)[1]),_60=[0,_5Y],_61=B(A(_5U,[_5V,_60,_])),_62=_61;return _60;},_63=function(_64){return E(_64);},_65=function(_66,_67,_68,_){var _69=B(A(_5k,[_68,_68,_])),_6a=_69,_6b=E(_6a),_6c=_6b[1],_6d=E(_6b[2]),_6e=_6d[2],_6f=E(_6d[4]),_6g=B(A(_66,[[0,_6d[1],_6e,_6d[3],[0,function(_){return new F(function(){return _5v(function(_6h,_){var _6i=B(A(_66,[new T(function(){var _6j=E(_6h);return [0,_6j[1],_6e,_6j[3],_6j[4],_6j[5],_6j[6],_6j[7]];}),_])),_6k=_6i;return [0,[0,_5t,E(E(_6k)[1])[2]],_6h];},_5s,_);});},function(_6l,_){var _6m=B(_5v(new T(function(){return B(A(_67,[_6l]));},1),_6c,_)),_6n=_6m,_6o=E(_6n);return _6o[0]==0?_28:B(A(_6f[2],[_6o[1],_]));}],_6d[5],_6d[6],_6d[7]],_])),_6p=_6g,_6q=E(_6p),_6r=_6q[2],_6s=E(_6q[1]),_6t=_6s[1],_6u=E(_6s[2]);if(!_6u[0]){return [0,[0,function(_6v,_){var _6w=B(A(_6t,[_6v,_])),_6x=_6w;if(!E(E(_68)[5])){var _6y=B(_5T(_63,_5t,_6v,_)),_6z=_6y,_6A=B(A(_5d,[_5q,_6z,_5p,_6c,_])),_6B=_6A;return _6v;}else{return _6v;}},_28],new T(function(){var _6C=E(_6r);return [0,_6C[1],_6C[2],_6C[3],_6f,_6C[5],_6C[6],_6C[7]];})];}else{var _6D=B(A(_67,[_6u[1],new T(function(){var _6E=E(_6r);return [0,_6E[1],_6E[2],_6E[3],_6f,_6E[5],_6E[6],_6E[7]];}),_])),_6F=_6D,_6G=E(_6F),_6H=E(_6G[1]),_6I=_6H[1];return [0,[0,function(_6J,_){var _6K=B(A(_6t,[_6J,_])),_6L=_6K;if(!E(E(_68)[5])){var _6M=B(_5T(_63,_6I,_6J,_)),_6N=_6M,_6O=B(A(_5d,[_5q,_6N,_5p,_6c,_])),_6P=_6O;return _6J;}else{var _6Q=B(A(_6I,[_6J,_])),_6R=_6Q;return _6J;}},_6H[2]],_6G[2]];}},_6S=function(_6T,_6U){switch(E(_6T)[0]){case 0:switch(E(_6U)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_6U)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_6U)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_6U)[0]==3?1:2;}},_6V=new T(function(){return B(unCStr("end of input"));}),_6W=new T(function(){return B(unCStr("unexpected"));}),_6X=new T(function(){return B(unCStr("expecting"));}),_6Y=new T(function(){return B(unCStr("unknown parse error"));}),_6Z=new T(function(){return B(unCStr("or"));}),_70=[0,58],_71=[0,34],_72=[0,41],_73=[1,_72,_9],_74=function(_75,_76,_77){var _78=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_e(B(_F(0,_76,_9)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_e(B(_F(0,_77,_9)),_73));})));},1)));})));}),_79=E(_75);return _79[0]==0?E(_78):[1,_71,new T(function(){return B(_e(_79,new T(function(){return B(unAppCStr("\" ",_78));},1)));})];},_7a=function(_7b,_7c){while(1){var _7d=E(_7b);if(!_7d[0]){return E(_7c)[0]==0?true:false;}else{var _7e=E(_7c);if(!_7e[0]){return false;}else{if(E(_7d[1])[1]!=E(_7e[1])[1]){return false;}else{_7b=_7d[2];_7c=_7e[2];continue;}}}}},_7f=function(_7g,_7h){return !B(_7a(_7g,_7h))?true:false;},_7i=[0,_7a,_7f],_7j=function(_7k,_7l,_7m){var _7n=E(_7m);if(!_7n[0]){return E(_7l);}else{return new F(function(){return _e(_7l,new T(function(){return B(_e(_7k,new T(function(){return B(_7j(_7k,_7n[1],_7n[2]));},1)));},1));});}},_7o=function(_7p){return E(_7p)[0]==0?false:true;},_7q=new T(function(){return B(unCStr(", "));}),_7r=function(_7s){var _7t=E(_7s);if(!_7t[0]){return [0];}else{return new F(function(){return _e(_7t[1],new T(function(){return B(_7r(_7t[2]));},1));});}},_7u=function(_7v,_7w){while(1){var _7x=(function(_7y,_7z){var _7A=E(_7z);if(!_7A[0]){return [0];}else{var _7B=_7A[1],_7C=_7A[2];if(!B(A(_7y,[_7B]))){var _7D=_7y;_7w=_7C;_7v=_7D;return null;}else{return [1,_7B,new T(function(){return B(_7u(_7y,_7C));})];}}})(_7v,_7w);if(_7x!=null){return _7x;}}},_7E=function(_7F,_7G){var _7H=E(_7G);return _7H[0]==0?[0]:[1,_7F,new T(function(){return B(_7E(_7H[1],_7H[2]));})];},_7I=function(_7J,_7K){while(1){var _7L=E(_7K);if(!_7L[0]){return E(_7J);}else{_7J=_7L[1];_7K=_7L[2];continue;}}},_7M=function(_7N){switch(E(_7N)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_7O=function(_7P){return E(_7P)[0]==1?true:false;},_7Q=function(_7R){return E(_7R)[0]==2?true:false;},_7S=[0,10],_7T=[1,_7S,_9],_7U=function(_7V){return new F(function(){return _e(_7T,_7V);});},_7W=[0,32],_7X=function(_7Y,_7Z){var _80=E(_7Z);return _80[0]==0?[0]:[1,new T(function(){return B(A(_7Y,[_80[1]]));}),new T(function(){return B(_7X(_7Y,_80[2]));})];},_81=function(_82){var _83=E(_82);switch(_83[0]){case 0:return E(_83[1]);case 1:return E(_83[1]);case 2:return E(_83[1]);default:return E(_83[1]);}},_84=function(_85){return E(E(_85)[1]);},_86=function(_87,_88,_89){while(1){var _8a=E(_89);if(!_8a[0]){return false;}else{if(!B(A(_84,[_87,_88,_8a[1]]))){_89=_8a[2];continue;}else{return true;}}}},_8b=function(_8c,_8d){var _8e=function(_8f,_8g){while(1){var _8h=(function(_8i,_8j){var _8k=E(_8i);if(!_8k[0]){return [0];}else{var _8l=_8k[1],_8m=_8k[2];if(!B(_86(_8c,_8l,_8j))){return [1,_8l,new T(function(){return B(_8e(_8m,[1,_8l,_8j]));})];}else{_8f=_8m;var _8n=_8j;_8g=_8n;return null;}}})(_8f,_8g);if(_8h!=null){return _8h;}}};return new F(function(){return _8e(_8d,_9);});},_8o=function(_8p,_8q,_8r,_8s,_8t,_8u){var _8v=E(_8u);if(!_8v[0]){return E(_8q);}else{var _8w=new T(function(){var _8x=B(_3g(_7M,_8v));return [0,_8x[1],_8x[2]];}),_8y=new T(function(){var _8z=B(_3g(_7O,E(_8w)[2]));return [0,_8z[1],_8z[2]];}),_8A=new T(function(){return E(E(_8y)[1]);}),_8B=function(_8C,_8D){var _8E=E(_8D);if(!_8E[0]){return E(_8C);}else{var _8F=new T(function(){return B(_e(_8p,[1,_7W,new T(function(){return B(_7I(_8C,_8E));})]));}),_8G=B(_8b(_7i,B(_7u(_7o,B(_7E(_8C,_8E))))));if(!_8G[0]){return new F(function(){return _e(_9,[1,_7W,_8F]);});}else{var _8H=_8G[1],_8I=E(_8G[2]);if(!_8I[0]){return new F(function(){return _e(_8H,[1,_7W,_8F]);});}else{return new F(function(){return _e(B(_e(_8H,new T(function(){return B(_e(_7q,new T(function(){return B(_7j(_7q,_8I[1],_8I[2]));},1)));},1))),[1,_7W,_8F]);});}}}},_8J=function(_8K,_8L){var _8M=B(_8b(_7i,B(_7u(_7o,B(_7X(_81,_8L))))));if(!_8M[0]){return [0];}else{var _8N=_8M[1],_8O=_8M[2],_8P=E(_8K);return _8P[0]==0?B(_8B(_8N,_8O)):B(_e(_8P,[1,_7W,new T(function(){return B(_8B(_8N,_8O));})]));}},_8Q=new T(function(){var _8R=B(_3g(_7Q,E(_8y)[2]));return [0,_8R[1],_8R[2]];});return new F(function(){return _7r(B(_7X(_7U,B(_8b(_7i,B(_7u(_7o,[1,new T(function(){if(!E(_8A)[0]){var _8S=E(E(_8w)[1]);if(!_8S[0]){var _8T=[0];}else{var _8U=E(_8S[1]);switch(_8U[0]){case 0:var _8V=E(_8U[1]),_8W=_8V[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8V]));break;case 1:var _8X=E(_8U[1]),_8W=_8X[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8X]));break;case 2:var _8Y=E(_8U[1]),_8W=_8Y[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8Y]));break;default:var _8Z=E(_8U[1]),_8W=_8Z[0]==0?B(_e(_8s,[1,_7W,_8t])):B(_e(_8s,[1,_7W,_8Z]));}var _8T=_8W;}var _90=_8T,_91=_90;}else{var _91=[0];}return _91;}),[1,new T(function(){return B(_8J(_8s,_8A));}),[1,new T(function(){return B(_8J(_8r,E(_8Q)[1]));}),[1,new T(function(){return B((function(_92){var _93=B(_8b(_7i,B(_7u(_7o,B(_7X(_81,_92))))));return _93[0]==0?[0]:B(_8B(_93[1],_93[2]));})(E(_8Q)[2]));}),_9]]]])))))));});}},_94=[1,_9,_9],_95=function(_96,_97){var _98=function(_99,_9a){var _9b=E(_99);if(!_9b[0]){return E(_9a);}else{var _9c=_9b[1],_9d=E(_9a);if(!_9d[0]){return E(_9b);}else{var _9e=_9d[1];return B(A(_96,[_9c,_9e]))==2?[1,_9e,new T(function(){return B(_98(_9b,_9d[2]));})]:[1,_9c,new T(function(){return B(_98(_9b[2],_9d));})];}}},_9f=function(_9g){var _9h=E(_9g);if(!_9h[0]){return [0];}else{var _9i=E(_9h[2]);return _9i[0]==0?E(_9h):[1,new T(function(){return B(_98(_9h[1],_9i[1]));}),new T(function(){return B(_9f(_9i[2]));})];}},_9j=function(_9k){while(1){var _9l=E(_9k);if(!_9l[0]){return E(new T(function(){return B(_9j(B(_9f(_9))));}));}else{if(!E(_9l[2])[0]){return E(_9l[1]);}else{_9k=B(_9f(_9l));continue;}}}},_9m=new T(function(){return B(_9n(_9));}),_9n=function(_9o){var _9p=E(_9o);if(!_9p[0]){return E(_94);}else{var _9q=_9p[1],_9r=E(_9p[2]);if(!_9r[0]){return [1,_9p,_9];}else{var _9s=_9r[1],_9t=_9r[2];if(B(A(_96,[_9q,_9s]))==2){return new F(function(){return (function(_9u,_9v,_9w){while(1){var _9x=(function(_9y,_9z,_9A){var _9B=E(_9A);if(!_9B[0]){return [1,[1,_9y,_9z],_9m];}else{var _9C=_9B[1];if(B(A(_96,[_9y,_9C]))==2){_9u=_9C;var _9D=[1,_9y,_9z];_9w=_9B[2];_9v=_9D;return null;}else{return [1,[1,_9y,_9z],new T(function(){return B(_9n(_9B));})];}}})(_9u,_9v,_9w);if(_9x!=null){return _9x;}}})(_9s,[1,_9q,_9],_9t);});}else{return new F(function(){return (function(_9E,_9F,_9G){while(1){var _9H=(function(_9I,_9J,_9K){var _9L=E(_9K);if(!_9L[0]){return [1,new T(function(){return B(A(_9J,[[1,_9I,_9]]));}),_9m];}else{var _9M=_9L[1],_9N=_9L[2];switch(B(A(_96,[_9I,_9M]))){case 0:_9E=_9M;_9F=function(_9O){return new F(function(){return A(_9J,[[1,_9I,_9O]]);});};_9G=_9N;return null;case 1:_9E=_9M;_9F=function(_9P){return new F(function(){return A(_9J,[[1,_9I,_9P]]);});};_9G=_9N;return null;default:return [1,new T(function(){return B(A(_9J,[[1,_9I,_9]]));}),new T(function(){return B(_9n(_9L));})];}}})(_9E,_9F,_9G);if(_9H!=null){return _9H;}}})(_9s,function(_9Q){return [1,_9q,_9Q];},_9t);});}}}};return new F(function(){return _9j(B(_9n(_97)));});},_9R=function(_9S,_9T,_9U,_9V){return new F(function(){return _e(B(_74(_9S,_9T,_9U)),[1,_70,new T(function(){return B(_8o(_6Z,_6Y,_6X,_6W,_6V,B(_95(_6S,_9V))));})]);});},_9W=function(_9X){var _9Y=E(_9X),_9Z=E(_9Y[1]);return new F(function(){return _9R(_9Z[1],_9Z[2],_9Z[3],_9Y[2]);});},_a0=new T(function(){return B(unCStr(" . "));}),_a1=function(_a2){var _a3=E(_a2);switch(_a3[0]){case 0:return E(_a3[3]);case 1:return E(_a3[3]);case 2:return E(_a3[3]);case 3:return E(_a3[3]);case 4:return E(_a3[3]);case 5:return E(_a3[3]);case 6:return E(_a3[3]);case 7:return E(_a3[3]);case 8:return E(_a3[3]);default:return E(_a3[3]);}},_a4=[0,41],_a5=[1,_a4,_9],_a6=new T(function(){return B(_3B("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_a7=[0,44],_a8=[0,40],_a9=function(_aa,_ab,_ac){var _ad=E(_ac);switch(_ad[0]){case 0:return E(_a6);case 1:return new F(function(){return A(_aa,[_ad[2],_9]);});break;case 2:return new F(function(){return _a1(_ad[2]);});break;case 3:return new F(function(){return A(_ab,[_ad[2],[1,new T(function(){return B(_a9(_aa,_ab,_ad[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_a1(_ad[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[3])),_a5));})]);});break;case 5:return new F(function(){return A(_ab,[_ad[2],[1,new T(function(){return B(_a9(_aa,_ab,_ad[3]));}),[1,new T(function(){return B(_a9(_aa,_ab,_ad[4]));}),_9]]]);});break;default:return new F(function(){return _e(B(_a1(_ad[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[3])),[1,_a7,new T(function(){return B(_e(B(_a9(_aa,_ab,_ad[4])),_a5));})]));})]);});}},_ae=[0],_af=function(_ag,_ah,_ai,_aj,_ak,_al,_am,_an){var _ao=E(_an);switch(_ao[0]){case 0:return [0];case 1:return new F(function(){return A(_aj,[_ao[2],_9]);});break;case 2:return new F(function(){return _a1(_ao[2]);});break;case 3:return new F(function(){return A(_ag,[_ao[2],[1,new T(function(){return B(_a9(_aj,_ak,_ao[3]));}),_9]]);});break;case 4:return new F(function(){return _e(B(_a1(_ao[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[3])),_a5));})]);});break;case 5:return new F(function(){return A(_ag,[_ao[2],[1,new T(function(){return B(_a9(_aj,_ak,_ao[3]));}),[1,new T(function(){return B(_a9(_aj,_ak,_ao[4]));}),_9]]]);});break;case 6:return new F(function(){return _e(B(_a1(_ao[2])),[1,_a8,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[3])),[1,_a7,new T(function(){return B(_e(B(_a9(_aj,_ak,_ao[4])),_a5));})]));})]);});break;case 7:return new F(function(){return A(_ah,[_ao[2],[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));}),_9]]);});break;case 8:return new F(function(){return _e(B(_a1(_ao[2])),new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));},1));});break;case 9:return new F(function(){return A(_ah,[_ao[2],[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3]));}),[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[4]));}),_9]]]);});break;case 10:return [1,_a8,new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[3])),new T(function(){return B(_e(B(_a1(_ao[2])),new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,_ao[4])),_a5));},1)));},1)));})];case 11:var _ap=_ao[2],_aq=_ao[3];return new F(function(){return A(_ai,[_ap,[1,new T(function(){return B(A(_al,[new T(function(){return B(A(_aq,[_ae]));}),_ap]));}),[1,new T(function(){return B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,B(A(_aq,[_ae]))));}),_9]]]);});break;default:var _ar=_ao[2],_as=_ao[3];return new F(function(){return _e(B(_a1(_ar)),new T(function(){return B(_e(B(A(_am,[new T(function(){return B(A(_as,[_ae]));}),_ar])),[1,_a8,new T(function(){return B(_e(B(_af(_ag,_ah,_ai,_aj,_ak,_al,_am,B(A(_as,[_ae])))),_a5));})]));},1));});}},_at=function(_au){var _av=E(_au);if(!_av[0]){return [0];}else{return new F(function(){return _e(_av[1],new T(function(){return B(_at(_av[2]));},1));});}},_aw=function(_ax,_ay){var _az=E(_ay);return _az[0]==0?[0]:[1,_ax,[1,_az[1],new T(function(){return B(_aw(_ax,_az[2]));})]];},_aA=function(_aB,_aC,_aD,_aE,_aF,_aG,_aH,_aI){var _aJ=E(_aI);if(!_aJ[0]){return new F(function(){return _a1(_aJ[1]);});}else{var _aK=B(_7X(function(_aL){return new F(function(){return _af(_aB,_aC,_aD,_aF,_aE,_aG,_aH,_aL);});},_aJ[1]));return _aK[0]==0?[0]:B(_at([1,_aK[1],new T(function(){return B(_aw(_a0,_aK[2]));})]));}},_aM=function(_aN,_aO,_aP,_aQ,_aR,_aS,_aT,_aU,_aV){return new F(function(){return _2T(function(_aW,_aX){return new F(function(){return _e(B(_aA(_aN,_aO,_aP,_aQ,_aR,_aS,_aT,_aW)),_aX);});},_aU,_aV);});},_aY=function(_aZ,_b0,_b1,_b2,_b3,_b4,_b5,_b6,_b7,_b8){return new F(function(){return _e(B(_aA(_aZ,_b0,_b1,_b2,_b3,_b4,_b5,_b7)),_b8);});},_b9=function(_ba,_bb,_bc,_bd,_be,_bf,_bg){return [0,function(_bh,_bi,_bj){return new F(function(){return _aY(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bh,_bi,_bj);});},function(_bj){return new F(function(){return _aA(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bj);});},function(_bi,_bj){return new F(function(){return _aM(_ba,_bb,_bc,_bd,_be,_bf,_bg,_bi,_bj);});}];},_bk=new T(function(){return B(unCStr(" . "));}),_bl=new T(function(){return B(unCStr(" \u2234 "));}),_bm=function(_bn){return E(E(_bn)[2]);},_bo=function(_bp,_bq,_br){var _bs=B(_7X(new T(function(){return B(_bm(_bp));}),_bq));if(!_bs[0]){return new F(function(){return _e(_bl,new T(function(){return B(A(_bm,[_bp,_br]));},1));});}else{return new F(function(){return _e(B(_at([1,_bs[1],new T(function(){return B(_aw(_bk,_bs[2]));})])),new T(function(){return B(_e(_bl,new T(function(){return B(A(_bm,[_bp,_br]));},1)));},1));});}},_bt=2,_bu=new T(function(){return B(unCStr("lined"));}),_bv=function(_bw,_){return [0,[0,_5t,[1,_bw]],_bw];},_bx=function(_by){return function(_bz,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bA=E(_by);return B(_e(B(_F(0,E(_bA[2])[1],_9)),_bA[1]));})]]],_bz];};},_bB=function(_bC,_){return new F(function(){return _65(_bv,_bx,_bC,_);});},_bD=function(_bE){return function(_bF,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bG=E(_bE);return B(_e(B(_F(0,E(_bG[2])[1],_9)),_bG[1]));})]]],_bF];};},_bH=function(_bC,_){return new F(function(){return _65(_bv,_bD,_bC,_);});},_bI=function(_bJ){return function(_bK,_){return [0,[0,_5t,[1,[1,_5j,new T(function(){var _bL=E(_bJ);return B(_e(B(_F(0,E(_bL[2])[1],_9)),_bL[1]));})]]],_bK];};},_bM=function(_bC,_){return new F(function(){return _65(_bv,_bI,_bC,_);});},_bN=new T(function(){return B(unCStr("rslt"));}),_bO=new T(function(){return B(unCStr("root"));}),_bP=new T(function(){return B(unCStr("class"));}),_bQ=new T(function(){return B(unCStr("analysis"));}),_bR=new T(function(){return B(unCStr("invalid"));}),_bS=function(_bC,_){return new F(function(){return _5T(_56,_bR,_bC,_);});},_bT=[1,_5c],_bU=[0,_bS,_bT],_bV=function(_bW,_){return [0,_bU,_bW];},_bX=new T(function(){return B(unCStr("span"));}),_bY=function(_bZ,_c0,_c1,_c2,_){var _c3=B(A(_c1,[_c2,_])),_c4=_c3,_c5=E(_c4),_c6=E(_c5[1]),_c7=_c6[1];return [0,[0,function(_c8,_){var _c9=jsFind(toJSStr(E(_bZ))),_ca=_c9,_cb=E(_ca);if(!_cb[0]){return _c8;}else{var _cc=_cb[1];switch(E(_c0)){case 0:var _cd=B(A(_c7,[_cc,_])),_ce=_cd;return _c8;case 1:var _cf=E(_cc),_cg=_cf[1],_ch=jsGetChildren(_cg),_ci=_ch,_cj=E(_ci);if(!_cj[0]){var _ck=B(A(_c7,[_cf,_])),_cl=_ck;return _c8;}else{var _cm=jsCreateElem(toJSStr(E(_bX))),_cn=_cm,_co=jsAddChildBefore(_cn,_cg,E(_cj[1])[1]),_cp=B(A(_c7,[[0,_cn],_])),_cq=_cp;return _c8;}break;default:var _cr=E(_cc),_cs=jsClearChildren(_cr[1]),_ct=B(A(_c7,[_cr,_])),_cu=_ct;return _c8;}}},_c6[2]],_c5[2]];},_cv=function(_cw,_cx){while(1){var _cy=E(_cw);if(!_cy[0]){return E(_cx)[0]==0?1:0;}else{var _cz=E(_cx);if(!_cz[0]){return 2;}else{var _cA=E(_cy[1])[1],_cB=E(_cz[1])[1];if(_cA!=_cB){return _cA>_cB?2:0;}else{_cw=_cy[2];_cx=_cz[2];continue;}}}}},_cC=new T(function(){return B(_e(_9,_9));}),_cD=function(_cE,_cF,_cG,_cH,_cI,_cJ,_cK,_cL){var _cM=[0,_cE,_cF,_cG],_cN=function(_cO){var _cP=E(_cH);if(!_cP[0]){var _cQ=E(_cL);if(!_cQ[0]){switch(B(_cv(_cE,_cI))){case 0:return [0,[0,_cI,_cJ,_cK],_9];case 1:return _cF>=_cJ?_cF!=_cJ?[0,_cM,_9]:_cG>=_cK?_cG!=_cK?[0,_cM,_9]:[0,_cM,_cC]:[0,[0,_cI,_cJ,_cK],_9]:[0,[0,_cI,_cJ,_cK],_9];default:return [0,_cM,_9];}}else{return [0,[0,_cI,_cJ,_cK],_cQ];}}else{switch(B(_cv(_cE,_cI))){case 0:return [0,[0,_cI,_cJ,_cK],_cL];case 1:return _cF>=_cJ?_cF!=_cJ?[0,_cM,_cP]:_cG>=_cK?_cG!=_cK?[0,_cM,_cP]:[0,_cM,new T(function(){return B(_e(_cP,_cL));})]:[0,[0,_cI,_cJ,_cK],_cL]:[0,[0,_cI,_cJ,_cK],_cL];default:return [0,_cM,_cP];}}};if(!E(_cL)[0]){var _cR=E(_cH);return _cR[0]==0?B(_cN(_)):[0,_cM,_cR];}else{return new F(function(){return _cN(_);});}},_cS=function(_cT,_cU){while(1){var _cV=E(_cT);if(!_cV[0]){return E(_cU);}else{_cT=_cV[2];var _cW=[1,_cV[1],_cU];_cU=_cW;continue;}}},_cX=new T(function(){return B(_cS(_9,_9));}),_cY=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_cZ=new T(function(){return B(err(_cY));}),_d0=function(_d1,_d2,_d3,_d4,_d5){var _d6=function(_d7,_d8,_d9){var _da=[1,_d8,_d7];return new F(function(){return A(_d1,[_d9,new T(function(){var _db=E(_d7);return function(_dc,_dd,_de){return new F(function(){return _d6(_da,_dc,_dd);});};}),_d4,_cZ,function(_df){return new F(function(){return A(_d3,[new T(function(){return B(_cS(_da,_9));}),_d9,new T(function(){var _dg=E(E(_d9)[2]),_dh=E(_df),_di=E(_dh[1]),_dj=B(_cD(_di[1],_di[2],_di[3],_dh[2],_dg[1],_dg[2],_dg[3],_9));return [0,E(_dj[1]),_dj[2]];})]);});}]);});};return new F(function(){return A(_d1,[_d2,function(_dk,_dl,_dm){return new F(function(){return _d6(_9,_dk,_dl);});},_d4,_cZ,function(_dn){return new F(function(){return A(_d5,[_cX,_d2,new T(function(){var _do=E(E(_d2)[2]),_dp=E(_dn),_dq=E(_dp[1]),_dr=B(_cD(_dq[1],_dq[2],_dq[3],_dp[2],_do[1],_do[2],_do[3],_9));return [0,E(_dr[1]),_dr[2]];})]);});}]);});},_ds=function(_dt,_du){var _dv=E(_dt),_dw=E(_dv[1]),_dx=E(_du),_dy=E(_dx[1]),_dz=B(_cD(_dw[1],_dw[2],_dw[3],_dv[2],_dy[1],_dy[2],_dy[3],_dx[2]));return [0,E(_dz[1]),_dz[2]];},_dA=function(_dB,_dC,_dD,_dE,_dF,_dG){var _dH=function(_dI,_dJ,_dK,_dL,_dM){return new F(function(){return _d0(_dB,_dJ,function(_dN,_dO,_dP){return new F(function(){return A(_dK,[[1,_dI,_dN],_dO,new T(function(){var _dQ=E(E(_dO)[2]),_dR=E(_dP),_dS=E(_dR[1]),_dT=B(_cD(_dS[1],_dS[2],_dS[3],_dR[2],_dQ[1],_dQ[2],_dQ[3],_9));return [0,E(_dT[1]),_dT[2]];})]);});},_dL,function(_dU,_dV,_dW){return new F(function(){return A(_dM,[[1,_dI,_dU],_dV,new T(function(){var _dX=E(E(_dV)[2]),_dY=E(_dW),_dZ=E(_dY[1]),_e0=B(_cD(_dZ[1],_dZ[2],_dZ[3],_dY[2],_dX[1],_dX[2],_dX[3],_9));return [0,E(_e0[1]),_e0[2]];})]);});});});};return new F(function(){return A(_dB,[_dC,function(_e1,_e2,_e3){return new F(function(){return _dH(_e1,_e2,_dD,_dE,function(_e4,_e5,_e6){return new F(function(){return A(_dD,[_e4,_e5,new T(function(){return B(_ds(_e3,_e6));})]);});});});},_dE,function(_e7,_e8,_e9){return new F(function(){return _dH(_e7,_e8,_dD,_dE,function(_ea,_eb,_ec){return new F(function(){return A(_dF,[_ea,_eb,new T(function(){return B(_ds(_e9,_ec));})]);});});});},_dG]);});},_ed=function(_ee,_ef,_eg,_eh,_ei){var _ej=function(_ek,_el){return new F(function(){return A(_ee,[_el,new T(function(){var _em=E(_ek);return function(_en,_eo,_ep){return new F(function(){return _ej(_9,_eo);});};}),_eh,_cZ,function(_eq){return new F(function(){return A(_eg,[_5c,_el,new T(function(){var _er=E(E(_el)[2]),_es=E(_eq),_et=E(_es[1]),_eu=B(_cD(_et[1],_et[2],_et[3],_es[2],_er[1],_er[2],_er[3],_9));return [0,E(_eu[1]),_eu[2]];})]);});}]);});};return new F(function(){return A(_ee,[_ef,function(_ev,_ew,_ex){return new F(function(){return _ej(_9,_ew);});},_eh,_cZ,function(_ey){return new F(function(){return A(_ei,[_5c,_ef,new T(function(){var _ez=E(E(_ef)[2]),_eA=E(_ey),_eB=E(_eA[1]),_eC=B(_cD(_eB[1],_eB[2],_eB[3],_eA[2],_ez[1],_ez[2],_ez[3],_9));return [0,E(_eC[1]),_eC[2]];})]);});}]);});},_eD=function(_eE,_eF,_eG,_eH,_eI,_eJ,_eK){var _eL=function(_eM,_eN,_eO,_eP,_eQ){var _eR=[1,_eM,_9],_eS=function(_eT,_eU,_eV,_eW){return new F(function(){return _eD(_eE,_eF,_eT,function(_eX,_eY,_eZ){return new F(function(){return A(_eU,[[1,_eM,_eX],_eY,new T(function(){var _f0=E(E(_eY)[2]),_f1=E(_eZ),_f2=E(_f1[1]),_f3=B(_cD(_f2[1],_f2[2],_f2[3],_f1[2],_f0[1],_f0[2],_f0[3],_9));return [0,E(_f3[1]),_f3[2]];})]);});},_eV,function(_f4,_f5,_f6){return new F(function(){return A(_eW,[[1,_eM,_f4],_f5,new T(function(){var _f7=E(E(_f5)[2]),_f8=E(_f6),_f9=E(_f8[1]),_fa=B(_cD(_f9[1],_f9[2],_f9[3],_f8[2],_f7[1],_f7[2],_f7[3],_9));return [0,E(_fa[1]),_fa[2]];})]);});},function(_fb){return new F(function(){return A(_eW,[_eR,_eT,new T(function(){var _fc=E(E(_eT)[2]),_fd=_fc[1],_fe=_fc[2],_ff=_fc[3],_fg=E(_fb),_fh=E(_fg[1]),_fi=B(_cD(_fh[1],_fh[2],_fh[3],_fg[2],_fd,_fe,_ff,_9)),_fj=E(_fi[1]),_fk=B(_cD(_fj[1],_fj[2],_fj[3],_fi[2],_fd,_fe,_ff,_9));return [0,E(_fk[1]),_fk[2]];})]);});});});};return new F(function(){return A(_eF,[_eN,function(_fl,_fm,_fn){return new F(function(){return _eS(_fm,_eO,_eP,function(_fo,_fp,_fq){return new F(function(){return A(_eO,[_fo,_fp,new T(function(){return B(_ds(_fn,_fq));})]);});});});},_eP,function(_fr,_fs,_ft){return new F(function(){return _eS(_fs,_eO,_eP,function(_fu,_fv,_fw){return new F(function(){return A(_eQ,[_fu,_fv,new T(function(){return B(_ds(_ft,_fw));})]);});});});},function(_fx){return new F(function(){return A(_eQ,[_eR,_eN,new T(function(){var _fy=E(E(_eN)[2]),_fz=E(_fx),_fA=E(_fz[1]),_fB=B(_cD(_fA[1],_fA[2],_fA[3],_fz[2],_fy[1],_fy[2],_fy[3],_9));return [0,E(_fB[1]),_fB[2]];})]);});}]);});};return new F(function(){return A(_eE,[_eG,function(_fC,_fD,_fE){return new F(function(){return _eL(_fC,_fD,_eH,_eI,function(_fF,_fG,_fH){return new F(function(){return A(_eH,[_fF,_fG,new T(function(){return B(_ds(_fE,_fH));})]);});});});},_eI,function(_fI,_fJ,_fK){return new F(function(){return _eL(_fI,_fJ,_eH,_eI,function(_fL,_fM,_fN){return new F(function(){return A(_eJ,[_fL,_fM,new T(function(){return B(_ds(_fK,_fN));})]);});});});},_eK]);});},_fO=function(_fP,_fQ){return new F(function(){return A(_fQ,[_fP]);});},_fR=[0,34],_fS=[1,_fR,_9],_fT=[0,E(_9)],_fU=[1,_fT,_9],_fV=function(_fW,_fX){var _fY=_fW%_fX;if(_fW<=0){if(_fW>=0){return E(_fY);}else{if(_fX<=0){return E(_fY);}else{var _fZ=E(_fY);return _fZ==0?0:_fZ+_fX|0;}}}else{if(_fX>=0){if(_fW>=0){return E(_fY);}else{if(_fX<=0){return E(_fY);}else{var _g0=E(_fY);return _g0==0?0:_g0+_fX|0;}}}else{var _g1=E(_fY);return _g1==0?0:_g1+_fX|0;}}},_g2=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_g3=new T(function(){return B(err(_g2));}),_g4=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_g5=new T(function(){return B(err(_g4));}),_g6=function(_g7,_g8){while(1){var _g9=E(_g7);if(!_g9[0]){return E(_g5);}else{var _ga=E(_g8);if(!_ga){return E(_g9[1]);}else{_g7=_g9[2];_g8=_ga-1|0;continue;}}}},_gb=new T(function(){return B(unCStr("ACK"));}),_gc=new T(function(){return B(unCStr("BEL"));}),_gd=new T(function(){return B(unCStr("BS"));}),_ge=new T(function(){return B(unCStr("SP"));}),_gf=[1,_ge,_9],_gg=new T(function(){return B(unCStr("US"));}),_gh=[1,_gg,_gf],_gi=new T(function(){return B(unCStr("RS"));}),_gj=[1,_gi,_gh],_gk=new T(function(){return B(unCStr("GS"));}),_gl=[1,_gk,_gj],_gm=new T(function(){return B(unCStr("FS"));}),_gn=[1,_gm,_gl],_go=new T(function(){return B(unCStr("ESC"));}),_gp=[1,_go,_gn],_gq=new T(function(){return B(unCStr("SUB"));}),_gr=[1,_gq,_gp],_gs=new T(function(){return B(unCStr("EM"));}),_gt=[1,_gs,_gr],_gu=new T(function(){return B(unCStr("CAN"));}),_gv=[1,_gu,_gt],_gw=new T(function(){return B(unCStr("ETB"));}),_gx=[1,_gw,_gv],_gy=new T(function(){return B(unCStr("SYN"));}),_gz=[1,_gy,_gx],_gA=new T(function(){return B(unCStr("NAK"));}),_gB=[1,_gA,_gz],_gC=new T(function(){return B(unCStr("DC4"));}),_gD=[1,_gC,_gB],_gE=new T(function(){return B(unCStr("DC3"));}),_gF=[1,_gE,_gD],_gG=new T(function(){return B(unCStr("DC2"));}),_gH=[1,_gG,_gF],_gI=new T(function(){return B(unCStr("DC1"));}),_gJ=[1,_gI,_gH],_gK=new T(function(){return B(unCStr("DLE"));}),_gL=[1,_gK,_gJ],_gM=new T(function(){return B(unCStr("SI"));}),_gN=[1,_gM,_gL],_gO=new T(function(){return B(unCStr("SO"));}),_gP=[1,_gO,_gN],_gQ=new T(function(){return B(unCStr("CR"));}),_gR=[1,_gQ,_gP],_gS=new T(function(){return B(unCStr("FF"));}),_gT=[1,_gS,_gR],_gU=new T(function(){return B(unCStr("VT"));}),_gV=[1,_gU,_gT],_gW=new T(function(){return B(unCStr("LF"));}),_gX=[1,_gW,_gV],_gY=new T(function(){return B(unCStr("HT"));}),_gZ=[1,_gY,_gX],_h0=[1,_gd,_gZ],_h1=[1,_gc,_h0],_h2=[1,_gb,_h1],_h3=new T(function(){return B(unCStr("ENQ"));}),_h4=[1,_h3,_h2],_h5=new T(function(){return B(unCStr("EOT"));}),_h6=[1,_h5,_h4],_h7=new T(function(){return B(unCStr("ETX"));}),_h8=[1,_h7,_h6],_h9=new T(function(){return B(unCStr("STX"));}),_ha=[1,_h9,_h8],_hb=new T(function(){return B(unCStr("SOH"));}),_hc=[1,_hb,_ha],_hd=new T(function(){return B(unCStr("NUL"));}),_he=[1,_hd,_hc],_hf=[0,92],_hg=new T(function(){return B(unCStr("\\DEL"));}),_hh=new T(function(){return B(unCStr("\\a"));}),_hi=new T(function(){return B(unCStr("\\\\"));}),_hj=new T(function(){return B(unCStr("\\SO"));}),_hk=new T(function(){return B(unCStr("\\r"));}),_hl=new T(function(){return B(unCStr("\\f"));}),_hm=new T(function(){return B(unCStr("\\v"));}),_hn=new T(function(){return B(unCStr("\\n"));}),_ho=new T(function(){return B(unCStr("\\t"));}),_hp=new T(function(){return B(unCStr("\\b"));}),_hq=function(_hr,_hs){if(_hr<=127){var _ht=E(_hr);switch(_ht){case 92:return new F(function(){return _e(_hi,_hs);});break;case 127:return new F(function(){return _e(_hg,_hs);});break;default:if(_ht<32){var _hu=E(_ht);switch(_hu){case 7:return new F(function(){return _e(_hh,_hs);});break;case 8:return new F(function(){return _e(_hp,_hs);});break;case 9:return new F(function(){return _e(_ho,_hs);});break;case 10:return new F(function(){return _e(_hn,_hs);});break;case 11:return new F(function(){return _e(_hm,_hs);});break;case 12:return new F(function(){return _e(_hl,_hs);});break;case 13:return new F(function(){return _e(_hk,_hs);});break;case 14:return new F(function(){return _e(_hj,new T(function(){var _hv=E(_hs);if(!_hv[0]){var _hw=[0];}else{var _hw=E(E(_hv[1])[1])==72?B(unAppCStr("\\&",_hv)):E(_hv);}return _hw;},1));});break;default:return new F(function(){return _e([1,_hf,new T(function(){var _hx=_hu;return _hx>=0?B(_g6(_he,_hx)):E(_g3);})],_hs);});}}else{return [1,[0,_ht],_hs];}}}else{return [1,_hf,new T(function(){var _hy=jsShowI(_hr),_hz=_hy;return B(_e(fromJSStr(_hz),new T(function(){var _hA=E(_hs);if(!_hA[0]){var _hB=[0];}else{var _hC=E(_hA[1])[1];if(_hC<48){var _hD=E(_hA);}else{var _hD=_hC>57?E(_hA):B(unAppCStr("\\&",_hA));}var _hE=_hD,_hF=_hE,_hB=_hF;}return _hB;},1)));})];}},_hG=new T(function(){return B(unCStr("\\\""));}),_hH=function(_hI,_hJ){var _hK=E(_hI);if(!_hK[0]){return E(_hJ);}else{var _hL=_hK[2],_hM=E(E(_hK[1])[1]);if(_hM==34){return new F(function(){return _e(_hG,new T(function(){return B(_hH(_hL,_hJ));},1));});}else{return new F(function(){return _hq(_hM,new T(function(){return B(_hH(_hL,_hJ));}));});}}},_hN=function(_hO,_hP,_hQ,_hR,_hS,_hT,_hU,_hV,_hW,_hX){var _hY=[0,_hS,_hT,_hU];return new F(function(){return A(_hO,[new T(function(){return B(A(_hP,[_hR]));}),function(_hZ){var _i0=E(_hZ);if(!_i0[0]){return E(new T(function(){return B(A(_hX,[[0,E(_hY),_fU]]));}));}else{var _i1=E(_i0[1]),_i2=_i1[1],_i3=_i1[2];if(!B(A(_hQ,[_i2]))){return new F(function(){return A(_hX,[[0,E(_hY),[1,[0,E([1,_fR,new T(function(){return B(_hH([1,_i2,_9],_fS));})])],_9]]]);});}else{var _i4=E(_i2);switch(E(_i4[1])){case 9:var _i5=[0,_hS,_hT,(_hU+8|0)-B(_fV(_hU-1|0,8))|0];break;case 10:var _i5=E([0,_hS,_hT+1|0,1]);break;default:var _i5=E([0,_hS,_hT,_hU+1|0]);}var _i6=_i5,_i7=[0,E(_i6),_9],_i8=[0,_i3,E(_i6),E(_hV)];return new F(function(){return A(_hW,[_i4,_i8,_i7]);});}}}]);});},_i9=function(_ia,_ib){return E(_ia)[1]!=E(_ib)[1];},_ic=function(_id,_ie){return E(_id)[1]==E(_ie)[1];},_if=[0,_ic,_i9],_ig=new T(function(){return B(unCStr(" 	"));}),_ih=function(_ii){return new F(function(){return _86(_if,_ii,_ig);});},_ij=function(_ik,_il){return E(_il);},_im=function(_in){return new F(function(){return err(_in);});},_io=function(_ip){return E(_ip);},_iq=[0,_fO,_ij,_io,_im],_ir=function(_is){return E(E(_is)[3]);},_it=function(_iu,_iv){var _iw=E(_iv);return _iw[0]==0?B(A(_ir,[_iu,_28])):B(A(_ir,[_iu,[1,[0,_iw[1],_iw[2]]]]));},_ix=function(_iy){return new F(function(){return _it(_iq,_iy);});},_iz=function(_iA,_iB,_iC,_iD,_iE){var _iF=E(_iA),_iG=E(_iF[2]);return new F(function(){return _hN(_fO,_ix,_ih,_iF[1],_iG[1],_iG[2],_iG[3],_iF[3],_iB,_iE);});},_iH=function(_iI){return [2,E(E(_iI))];},_iJ=function(_iK,_iL){switch(E(_iK)[0]){case 0:switch(E(_iL)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_iL)[0]==1?false:true;case 2:return E(_iL)[0]==2?false:true;default:return E(_iL)[0]==3?false:true;}},_iM=[2,E(_9)],_iN=function(_iO){return new F(function(){return _iJ(_iM,_iO);});},_iP=function(_iQ,_iR,_iS){var _iT=E(_iS);if(!_iT[0]){return [0,_iQ,[1,_iM,new T(function(){return B(_7u(_iN,_iR));})]];}else{var _iU=_iT[1],_iV=E(_iT[2]);if(!_iV[0]){var _iW=new T(function(){return [2,E(E(_iU))];});return [0,_iQ,[1,_iW,new T(function(){return B(_7u(function(_iO){return new F(function(){return _iJ(_iW,_iO);});},_iR));})]];}else{var _iX=new T(function(){return [2,E(E(_iU))];}),_iY=function(_iZ){var _j0=E(_iZ);if(!_j0[0]){return [0,_iQ,[1,_iX,new T(function(){return B(_7u(function(_iO){return new F(function(){return _iJ(_iX,_iO);});},_iR));})]];}else{var _j1=B(_iY(_j0[2]));return [0,_j1[1],[1,new T(function(){return B(_iH(_j0[1]));}),_j1[2]]];}};return new F(function(){return (function(_j2,_j3){var _j4=B(_iY(_j3));return [0,_j4[1],[1,new T(function(){return B(_iH(_j2));}),_j4[2]]];})(_iV[1],_iV[2]);});}}},_j5=function(_j6,_j7){var _j8=E(_j6),_j9=B(_iP(_j8[1],_j8[2],_j7));return [0,E(_j9[1]),_j9[2]];},_ja=function(_jb,_jc,_jd,_je,_jf,_jg,_jh){return new F(function(){return A(_jb,[_jd,_je,_jf,function(_ji,_jj,_jk){return new F(function(){return A(_jg,[_ji,_jj,new T(function(){var _jl=E(_jk),_jm=E(_jl[2]);if(!_jm[0]){var _jn=E(_jl);}else{var _jo=B(_iP(_jl[1],_jm,_jc)),_jn=[0,E(_jo[1]),_jo[2]];}var _jp=_jn;return _jp;})]);});},function(_jq){return new F(function(){return A(_jh,[new T(function(){return B(_j5(_jq,_jc));})]);});}]);});},_jr=new T(function(){return B(unCStr("digit"));}),_js=[1,_jr,_9],_jt=function(_ju){return new F(function(){return _it(_iq,_ju);});},_jv=function(_jw){var _jx=E(_jw)[1];return _jx<48?false:_jx<=57;},_jy=function(_jz,_jA,_jB,_jC,_jD){var _jE=E(_jz),_jF=E(_jE[2]);return new F(function(){return _hN(_fO,_jt,_jv,_jE[1],_jF[1],_jF[2],_jF[3],_jE[3],_jA,_jD);});},_jG=function(_jH,_jI,_jJ,_jK,_jL){return new F(function(){return _ja(_jy,_js,_jH,_jI,_jJ,_jK,_jL);});},_jM=function(_jN,_jO,_jP,_jQ,_jR){return new F(function(){return _dA(_jG,_jN,_jO,_jP,_jQ,_jR);});},_jS=function(_jT){return [0,_jT,function(_iO){return new F(function(){return _it(_jT,_iO);});}];},_jU=new T(function(){return B(_jS(_iq));}),_jV=function(_jW,_jX){return function(_jY,_jZ,_k0,_k1,_k2){return new F(function(){return _ja(function(_k3,_k4,_k5,_k6,_k7){var _k8=E(_jW),_k9=E(_k3),_ka=E(_k9[2]);return new F(function(){return _hN(E(_k8[1])[1],_k8[2],function(_kb){return new F(function(){return _ic(_kb,_jX);});},_k9[1],_ka[1],_ka[2],_ka[3],_k9[3],_k4,_k7);});},[1,[1,_fR,new T(function(){return B(_hH([1,_jX,_9],_fS));})],_9],_jY,_jZ,_k0,_k1,_k2);});};},_kc=[0,44],_kd=new T(function(){return B(_jV(_jU,_kc));}),_ke=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_kf=new T(function(){return B(err(_ke));}),_kg=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_kh=new T(function(){return B(err(_kg));}),_ki=new T(function(){return B(_3B("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_kj=function(_kk,_kl){while(1){var _km=(function(_kn,_ko){var _kp=E(_kn);switch(_kp[0]){case 0:var _kq=E(_ko);if(!_kq[0]){return [0];}else{_kk=B(A(_kp[1],[_kq[1]]));_kl=_kq[2];return null;}break;case 1:var _kr=B(A(_kp[1],[_ko])),_ks=_ko;_kk=_kr;_kl=_ks;return null;case 2:return [0];case 3:return [1,[0,_kp[1],_ko],new T(function(){return B(_kj(_kp[2],_ko));})];default:return E(_kp[1]);}})(_kk,_kl);if(_km!=null){return _km;}}},_kt=function(_ku,_kv){var _kw=function(_kx){var _ky=E(_kv);if(_ky[0]==3){return [3,_ky[1],new T(function(){return B(_kt(_ku,_ky[2]));})];}else{var _kz=E(_ku);if(_kz[0]==2){return E(_ky);}else{var _kA=E(_ky);if(_kA[0]==2){return E(_kz);}else{var _kB=function(_kC){var _kD=E(_kA);if(_kD[0]==4){return [1,function(_kE){return [4,new T(function(){return B(_e(B(_kj(_kz,_kE)),_kD[1]));})];}];}else{var _kF=E(_kz);if(_kF[0]==1){var _kG=_kF[1],_kH=E(_kD);return _kH[0]==0?[1,function(_kI){return new F(function(){return _kt(B(A(_kG,[_kI])),_kH);});}]:[1,function(_kJ){return new F(function(){return _kt(B(A(_kG,[_kJ])),new T(function(){return B(A(_kH[1],[_kJ]));}));});}];}else{var _kK=E(_kD);return _kK[0]==0?E(_ki):[1,function(_kL){return new F(function(){return _kt(_kF,new T(function(){return B(A(_kK[1],[_kL]));}));});}];}}},_kM=E(_kz);switch(_kM[0]){case 1:var _kN=E(_kA);if(_kN[0]==4){return [1,function(_kO){return [4,new T(function(){return B(_e(B(_kj(B(A(_kM[1],[_kO])),_kO)),_kN[1]));})];}];}else{return new F(function(){return _kB(_);});}break;case 4:var _kP=_kM[1],_kQ=E(_kA);switch(_kQ[0]){case 0:return [1,function(_kR){return [4,new T(function(){return B(_e(_kP,new T(function(){return B(_kj(_kQ,_kR));},1)));})];}];case 1:return [1,function(_kS){return [4,new T(function(){return B(_e(_kP,new T(function(){return B(_kj(B(A(_kQ[1],[_kS])),_kS));},1)));})];}];default:return [4,new T(function(){return B(_e(_kP,_kQ[1]));})];}break;default:return new F(function(){return _kB(_);});}}}}},_kT=E(_ku);switch(_kT[0]){case 0:var _kU=E(_kv);if(!_kU[0]){return [0,function(_kV){return new F(function(){return _kt(B(A(_kT[1],[_kV])),new T(function(){return B(A(_kU[1],[_kV]));}));});}];}else{return new F(function(){return _kw(_);});}break;case 3:return [3,_kT[1],new T(function(){return B(_kt(_kT[2],_kv));})];default:return new F(function(){return _kw(_);});}},_kW=[0,41],_kX=[1,_kW,_9],_kY=[0,40],_kZ=[1,_kY,_9],_l0=function(_l1,_l2){while(1){var _l3=E(_l1);if(!_l3[0]){return E(_l2)[0]==0?true:false;}else{var _l4=E(_l2);if(!_l4[0]){return false;}else{if(E(_l3[1])[1]!=E(_l4[1])[1]){return false;}else{_l1=_l3[2];_l2=_l4[2];continue;}}}}},_l5=function(_l6,_l7){var _l8=E(_l6);switch(_l8[0]){case 0:return [0,function(_l9){return new F(function(){return _l5(B(A(_l8[1],[_l9])),_l7);});}];case 1:return [1,function(_la){return new F(function(){return _l5(B(A(_l8[1],[_la])),_l7);});}];case 2:return [2];case 3:return new F(function(){return _kt(B(A(_l7,[_l8[1]])),new T(function(){return B(_l5(_l8[2],_l7));}));});break;default:var _lb=function(_lc){var _ld=E(_lc);if(!_ld[0]){return [0];}else{var _le=E(_ld[1]);return new F(function(){return _e(B(_kj(B(A(_l7,[_le[1]])),_le[2])),new T(function(){return B(_lb(_ld[2]));},1));});}},_lf=B(_lb(_l8[1]));return _lf[0]==0?[2]:[4,_lf];}},_lg=[2],_lh=function(_li){return [3,_li,_lg];},_lj=function(_lk,_ll){var _lm=E(_lk);if(!_lm){return new F(function(){return A(_ll,[_5c]);});}else{return [0,function(_ln){return E(new T(function(){return B(_lj(_lm-1|0,_ll));}));}];}},_lo=function(_lp,_lq,_lr){return function(_ls){return new F(function(){return A(function(_lt,_lu,_lv){while(1){var _lw=(function(_lx,_ly,_lz){var _lA=E(_lx);switch(_lA[0]){case 0:var _lB=E(_ly);if(!_lB[0]){return E(_lq);}else{_lt=B(A(_lA[1],[_lB[1]]));_lu=_lB[2];var _lC=_lz+1|0;_lv=_lC;return null;}break;case 1:var _lD=B(A(_lA[1],[_ly])),_lE=_ly,_lC=_lz;_lt=_lD;_lu=_lE;_lv=_lC;return null;case 2:return E(_lq);case 3:return function(_lF){return new F(function(){return _lj(_lz,function(_lG){return E(new T(function(){return B(_l5(_lA,_lF));}));});});};default:return function(_lH){return new F(function(){return _l5(_lA,_lH);});};}})(_lt,_lu,_lv);if(_lw!=null){return _lw;}}},[new T(function(){return B(A(_lp,[_lh]));}),_ls,0,_lr]);});};},_lI=function(_lJ){return new F(function(){return A(_lJ,[_9]);});},_lK=function(_lL,_lM){var _lN=function(_lO){var _lP=E(_lO);if(!_lP[0]){return E(_lI);}else{var _lQ=_lP[1];return !B(A(_lL,[_lQ]))?E(_lI):function(_lR){return [0,function(_lS){return E(new T(function(){return B(A(new T(function(){return B(_lN(_lP[2]));}),[function(_lT){return new F(function(){return A(_lR,[[1,_lQ,_lT]]);});}]));}));}];};}};return function(_lU){return new F(function(){return A(_lN,[_lU,_lM]);});};},_lV=[6],_lW=new T(function(){return B(unCStr("valDig: Bad base"));}),_lX=new T(function(){return B(err(_lW));}),_lY=function(_lZ,_m0){var _m1=function(_m2,_m3){var _m4=E(_m2);if(!_m4[0]){return function(_m5){return new F(function(){return A(_m5,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{var _m6=E(_m4[1])[1],_m7=function(_m8){return function(_m9){return [0,function(_ma){return E(new T(function(){return B(A(new T(function(){return B(_m1(_m4[2],function(_mb){return new F(function(){return A(_m3,[[1,_m8,_mb]]);});}));}),[_m9]));}));}];};};switch(E(E(_lZ)[1])){case 8:if(48>_m6){return function(_mc){return new F(function(){return A(_mc,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{if(_m6>55){return function(_md){return new F(function(){return A(_md,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{return new F(function(){return _m7([0,_m6-48|0]);});}}break;case 10:if(48>_m6){return function(_me){return new F(function(){return A(_me,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{if(_m6>57){return function(_mf){return new F(function(){return A(_mf,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{return new F(function(){return _m7([0,_m6-48|0]);});}}break;case 16:if(48>_m6){if(97>_m6){if(65>_m6){return function(_mg){return new F(function(){return A(_mg,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{if(_m6>70){return function(_mh){return new F(function(){return A(_mh,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{return new F(function(){return _m7([0,(_m6-65|0)+10|0]);});}}}else{if(_m6>102){if(65>_m6){return function(_mi){return new F(function(){return A(_mi,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{if(_m6>70){return function(_mj){return new F(function(){return A(_mj,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{return new F(function(){return _m7([0,(_m6-65|0)+10|0]);});}}}else{return new F(function(){return _m7([0,(_m6-97|0)+10|0]);});}}}else{if(_m6>57){if(97>_m6){if(65>_m6){return function(_mk){return new F(function(){return A(_mk,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{if(_m6>70){return function(_ml){return new F(function(){return A(_ml,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{return new F(function(){return _m7([0,(_m6-65|0)+10|0]);});}}}else{if(_m6>102){if(65>_m6){return function(_mm){return new F(function(){return A(_mm,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{if(_m6>70){return function(_mn){return new F(function(){return A(_mn,[new T(function(){return B(A(_m3,[_9]));})]);});};}else{return new F(function(){return _m7([0,(_m6-65|0)+10|0]);});}}}else{return new F(function(){return _m7([0,(_m6-97|0)+10|0]);});}}}else{return new F(function(){return _m7([0,_m6-48|0]);});}}break;default:return E(_lX);}}};return function(_mo){return new F(function(){return A(_m1,[_mo,_5q,function(_mp){var _mq=E(_mp);return _mq[0]==0?[2]:B(A(_m0,[_mq]));}]);});};},_mr=[0,10],_ms=[0,1],_mt=[0,2147483647],_mu=function(_mv,_mw){while(1){var _mx=E(_mv);if(!_mx[0]){var _my=_mx[1],_mz=E(_mw);if(!_mz[0]){var _mA=_mz[1],_mB=addC(_my,_mA);if(!E(_mB[2])){return [0,_mB[1]];}else{_mv=[1,I_fromInt(_my)];_mw=[1,I_fromInt(_mA)];continue;}}else{_mv=[1,I_fromInt(_my)];_mw=_mz;continue;}}else{var _mC=E(_mw);if(!_mC[0]){_mv=_mx;_mw=[1,I_fromInt(_mC[1])];continue;}else{return [1,I_add(_mx[1],_mC[1])];}}}},_mD=new T(function(){return B(_mu(_mt,_ms));}),_mE=function(_mF){var _mG=E(_mF);if(!_mG[0]){var _mH=E(_mG[1]);return _mH==(-2147483648)?E(_mD):[0, -_mH];}else{return [1,I_negate(_mG[1])];}},_mI=[0,10],_mJ=[0,0],_mK=function(_mL){return [0,_mL];},_mM=function(_mN,_mO){while(1){var _mP=E(_mN);if(!_mP[0]){var _mQ=_mP[1],_mR=E(_mO);if(!_mR[0]){var _mS=_mR[1];if(!(imul(_mQ,_mS)|0)){return [0,imul(_mQ,_mS)|0];}else{_mN=[1,I_fromInt(_mQ)];_mO=[1,I_fromInt(_mS)];continue;}}else{_mN=[1,I_fromInt(_mQ)];_mO=_mR;continue;}}else{var _mT=E(_mO);if(!_mT[0]){_mN=_mP;_mO=[1,I_fromInt(_mT[1])];continue;}else{return [1,I_mul(_mP[1],_mT[1])];}}}},_mU=function(_mV,_mW,_mX){while(1){var _mY=E(_mX);if(!_mY[0]){return E(_mW);}else{var _mZ=B(_mu(B(_mM(_mW,_mV)),B(_mK(E(_mY[1])[1]))));_mX=_mY[2];_mW=_mZ;continue;}}},_n0=function(_n1){var _n2=new T(function(){return B(_kt(B(_kt([0,function(_n3){return E(E(_n3)[1])==45?[1,B(_lY(_mr,function(_n4){return new F(function(){return A(_n1,[[1,new T(function(){return B(_mE(B(_mU(_mI,_mJ,_n4))));})]]);});}))]:[2];}],[0,function(_n5){return E(E(_n5)[1])==43?[1,B(_lY(_mr,function(_n6){return new F(function(){return A(_n1,[[1,new T(function(){return B(_mU(_mI,_mJ,_n6));})]]);});}))]:[2];}])),new T(function(){return [1,B(_lY(_mr,function(_n7){return new F(function(){return A(_n1,[[1,new T(function(){return B(_mU(_mI,_mJ,_n7));})]]);});}))];})));});return new F(function(){return _kt([0,function(_n8){return E(E(_n8)[1])==101?E(_n2):[2];}],[0,function(_n9){return E(E(_n9)[1])==69?E(_n2):[2];}]);});},_na=function(_nb){return new F(function(){return A(_nb,[_28]);});},_nc=function(_nd){return new F(function(){return A(_nd,[_28]);});},_ne=function(_nf){return function(_ng){return E(E(_ng)[1])==46?[1,B(_lY(_mr,function(_nh){return new F(function(){return A(_nf,[[1,_nh]]);});}))]:[2];};},_ni=function(_nj){return [0,B(_ne(_nj))];},_nk=function(_nl){return new F(function(){return _lY(_mr,function(_nm){return [1,B(_lo(_ni,_na,function(_nn){return [1,B(_lo(_n0,_nc,function(_no){return new F(function(){return A(_nl,[[5,[1,_nm,_nn,_no]]]);});}))];}))];});});},_np=function(_nq){return [1,B(_nk(_nq))];},_nr=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_ns=function(_nt){return new F(function(){return _86(_if,_nt,_nr);});},_nu=[0,8],_nv=[0,16],_nw=function(_nx){var _ny=function(_nz){return new F(function(){return A(_nx,[[5,[0,_nu,_nz]]]);});},_nA=function(_nB){return new F(function(){return A(_nx,[[5,[0,_nv,_nB]]]);});};return function(_nC){return E(E(_nC)[1])==48?E([0,function(_nD){switch(E(E(_nD)[1])){case 79:return [1,B(_lY(_nu,_ny))];case 88:return [1,B(_lY(_nv,_nA))];case 111:return [1,B(_lY(_nu,_ny))];case 120:return [1,B(_lY(_nv,_nA))];default:return [2];}}]):[2];};},_nE=function(_nF){return [0,B(_nw(_nF))];},_nG=true,_nH=function(_nI){var _nJ=new T(function(){return B(A(_nI,[_nu]));}),_nK=new T(function(){return B(A(_nI,[_nv]));});return function(_nL){switch(E(E(_nL)[1])){case 79:return E(_nJ);case 88:return E(_nK);case 111:return E(_nJ);case 120:return E(_nK);default:return [2];}};},_nM=function(_nN){return [0,B(_nH(_nN))];},_nO=[0,92],_nP=function(_nQ){return new F(function(){return A(_nQ,[_mr]);});},_nR=function(_nS){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_F(9,_nS,_9));}))));});},_nT=function(_nU){var _nV=E(_nU);return _nV[0]==0?E(_nV[1]):I_toInt(_nV[1]);},_nW=function(_nX,_nY){var _nZ=E(_nX);if(!_nZ[0]){var _o0=_nZ[1],_o1=E(_nY);return _o1[0]==0?_o0<=_o1[1]:I_compareInt(_o1[1],_o0)>=0;}else{var _o2=_nZ[1],_o3=E(_nY);return _o3[0]==0?I_compareInt(_o2,_o3[1])<=0:I_compare(_o2,_o3[1])<=0;}},_o4=function(_o5){return [2];},_o6=function(_o7){var _o8=E(_o7);if(!_o8[0]){return E(_o4);}else{var _o9=_o8[1],_oa=E(_o8[2]);return _oa[0]==0?E(_o9):function(_ob){return new F(function(){return _kt(B(A(_o9,[_ob])),new T(function(){return B(A(new T(function(){return B(_o6(_oa));}),[_ob]));}));});};}},_oc=function(_od){return [2];},_oe=function(_of,_og){var _oh=function(_oi,_oj){var _ok=E(_oi);if(!_ok[0]){return function(_ol){return new F(function(){return A(_ol,[_of]);});};}else{var _om=E(_oj);return _om[0]==0?E(_oc):E(_ok[1])[1]!=E(_om[1])[1]?E(_oc):function(_on){return [0,function(_oo){return E(new T(function(){return B(A(new T(function(){return B(_oh(_ok[2],_om[2]));}),[_on]));}));}];};}};return function(_op){return new F(function(){return A(_oh,[_of,_op,_og]);});};},_oq=new T(function(){return B(unCStr("SOH"));}),_or=[0,1],_os=function(_ot){return [1,B(_oe(_oq,function(_ou){return E(new T(function(){return B(A(_ot,[_or]));}));}))];},_ov=new T(function(){return B(unCStr("SO"));}),_ow=[0,14],_ox=function(_oy){return [1,B(_oe(_ov,function(_oz){return E(new T(function(){return B(A(_oy,[_ow]));}));}))];},_oA=function(_oB){return [1,B(_lo(_os,_ox,_oB))];},_oC=new T(function(){return B(unCStr("NUL"));}),_oD=[0,0],_oE=function(_oF){return [1,B(_oe(_oC,function(_oG){return E(new T(function(){return B(A(_oF,[_oD]));}));}))];},_oH=new T(function(){return B(unCStr("STX"));}),_oI=[0,2],_oJ=function(_oK){return [1,B(_oe(_oH,function(_oL){return E(new T(function(){return B(A(_oK,[_oI]));}));}))];},_oM=new T(function(){return B(unCStr("ETX"));}),_oN=[0,3],_oO=function(_oP){return [1,B(_oe(_oM,function(_oQ){return E(new T(function(){return B(A(_oP,[_oN]));}));}))];},_oR=new T(function(){return B(unCStr("EOT"));}),_oS=[0,4],_oT=function(_oU){return [1,B(_oe(_oR,function(_oV){return E(new T(function(){return B(A(_oU,[_oS]));}));}))];},_oW=new T(function(){return B(unCStr("ENQ"));}),_oX=[0,5],_oY=function(_oZ){return [1,B(_oe(_oW,function(_p0){return E(new T(function(){return B(A(_oZ,[_oX]));}));}))];},_p1=new T(function(){return B(unCStr("ACK"));}),_p2=[0,6],_p3=function(_p4){return [1,B(_oe(_p1,function(_p5){return E(new T(function(){return B(A(_p4,[_p2]));}));}))];},_p6=new T(function(){return B(unCStr("BEL"));}),_p7=[0,7],_p8=function(_p9){return [1,B(_oe(_p6,function(_pa){return E(new T(function(){return B(A(_p9,[_p7]));}));}))];},_pb=new T(function(){return B(unCStr("BS"));}),_pc=[0,8],_pd=function(_pe){return [1,B(_oe(_pb,function(_pf){return E(new T(function(){return B(A(_pe,[_pc]));}));}))];},_pg=new T(function(){return B(unCStr("HT"));}),_ph=[0,9],_pi=function(_pj){return [1,B(_oe(_pg,function(_pk){return E(new T(function(){return B(A(_pj,[_ph]));}));}))];},_pl=new T(function(){return B(unCStr("LF"));}),_pm=[0,10],_pn=function(_po){return [1,B(_oe(_pl,function(_pp){return E(new T(function(){return B(A(_po,[_pm]));}));}))];},_pq=new T(function(){return B(unCStr("VT"));}),_pr=[0,11],_ps=function(_pt){return [1,B(_oe(_pq,function(_pu){return E(new T(function(){return B(A(_pt,[_pr]));}));}))];},_pv=new T(function(){return B(unCStr("FF"));}),_pw=[0,12],_px=function(_py){return [1,B(_oe(_pv,function(_pz){return E(new T(function(){return B(A(_py,[_pw]));}));}))];},_pA=new T(function(){return B(unCStr("CR"));}),_pB=[0,13],_pC=function(_pD){return [1,B(_oe(_pA,function(_pE){return E(new T(function(){return B(A(_pD,[_pB]));}));}))];},_pF=new T(function(){return B(unCStr("SI"));}),_pG=[0,15],_pH=function(_pI){return [1,B(_oe(_pF,function(_pJ){return E(new T(function(){return B(A(_pI,[_pG]));}));}))];},_pK=new T(function(){return B(unCStr("DLE"));}),_pL=[0,16],_pM=function(_pN){return [1,B(_oe(_pK,function(_pO){return E(new T(function(){return B(A(_pN,[_pL]));}));}))];},_pP=new T(function(){return B(unCStr("DC1"));}),_pQ=[0,17],_pR=function(_pS){return [1,B(_oe(_pP,function(_pT){return E(new T(function(){return B(A(_pS,[_pQ]));}));}))];},_pU=new T(function(){return B(unCStr("DC2"));}),_pV=[0,18],_pW=function(_pX){return [1,B(_oe(_pU,function(_pY){return E(new T(function(){return B(A(_pX,[_pV]));}));}))];},_pZ=new T(function(){return B(unCStr("DC3"));}),_q0=[0,19],_q1=function(_q2){return [1,B(_oe(_pZ,function(_q3){return E(new T(function(){return B(A(_q2,[_q0]));}));}))];},_q4=new T(function(){return B(unCStr("DC4"));}),_q5=[0,20],_q6=function(_q7){return [1,B(_oe(_q4,function(_q8){return E(new T(function(){return B(A(_q7,[_q5]));}));}))];},_q9=new T(function(){return B(unCStr("NAK"));}),_qa=[0,21],_qb=function(_qc){return [1,B(_oe(_q9,function(_qd){return E(new T(function(){return B(A(_qc,[_qa]));}));}))];},_qe=new T(function(){return B(unCStr("SYN"));}),_qf=[0,22],_qg=function(_qh){return [1,B(_oe(_qe,function(_qi){return E(new T(function(){return B(A(_qh,[_qf]));}));}))];},_qj=new T(function(){return B(unCStr("ETB"));}),_qk=[0,23],_ql=function(_qm){return [1,B(_oe(_qj,function(_qn){return E(new T(function(){return B(A(_qm,[_qk]));}));}))];},_qo=new T(function(){return B(unCStr("CAN"));}),_qp=[0,24],_qq=function(_qr){return [1,B(_oe(_qo,function(_qs){return E(new T(function(){return B(A(_qr,[_qp]));}));}))];},_qt=new T(function(){return B(unCStr("EM"));}),_qu=[0,25],_qv=function(_qw){return [1,B(_oe(_qt,function(_qx){return E(new T(function(){return B(A(_qw,[_qu]));}));}))];},_qy=new T(function(){return B(unCStr("SUB"));}),_qz=[0,26],_qA=function(_qB){return [1,B(_oe(_qy,function(_qC){return E(new T(function(){return B(A(_qB,[_qz]));}));}))];},_qD=new T(function(){return B(unCStr("ESC"));}),_qE=[0,27],_qF=function(_qG){return [1,B(_oe(_qD,function(_qH){return E(new T(function(){return B(A(_qG,[_qE]));}));}))];},_qI=new T(function(){return B(unCStr("FS"));}),_qJ=[0,28],_qK=function(_qL){return [1,B(_oe(_qI,function(_qM){return E(new T(function(){return B(A(_qL,[_qJ]));}));}))];},_qN=new T(function(){return B(unCStr("GS"));}),_qO=[0,29],_qP=function(_qQ){return [1,B(_oe(_qN,function(_qR){return E(new T(function(){return B(A(_qQ,[_qO]));}));}))];},_qS=new T(function(){return B(unCStr("RS"));}),_qT=[0,30],_qU=function(_qV){return [1,B(_oe(_qS,function(_qW){return E(new T(function(){return B(A(_qV,[_qT]));}));}))];},_qX=new T(function(){return B(unCStr("US"));}),_qY=[0,31],_qZ=function(_r0){return [1,B(_oe(_qX,function(_r1){return E(new T(function(){return B(A(_r0,[_qY]));}));}))];},_r2=new T(function(){return B(unCStr("SP"));}),_r3=[0,32],_r4=function(_r5){return [1,B(_oe(_r2,function(_r6){return E(new T(function(){return B(A(_r5,[_r3]));}));}))];},_r7=new T(function(){return B(unCStr("DEL"));}),_r8=[0,127],_r9=function(_ra){return [1,B(_oe(_r7,function(_rb){return E(new T(function(){return B(A(_ra,[_r8]));}));}))];},_rc=[1,_r9,_9],_rd=[1,_r4,_rc],_re=[1,_qZ,_rd],_rf=[1,_qU,_re],_rg=[1,_qP,_rf],_rh=[1,_qK,_rg],_ri=[1,_qF,_rh],_rj=[1,_qA,_ri],_rk=[1,_qv,_rj],_rl=[1,_qq,_rk],_rm=[1,_ql,_rl],_rn=[1,_qg,_rm],_ro=[1,_qb,_rn],_rp=[1,_q6,_ro],_rq=[1,_q1,_rp],_rr=[1,_pW,_rq],_rs=[1,_pR,_rr],_rt=[1,_pM,_rs],_ru=[1,_pH,_rt],_rv=[1,_pC,_ru],_rw=[1,_px,_rv],_rx=[1,_ps,_rw],_ry=[1,_pn,_rx],_rz=[1,_pi,_ry],_rA=[1,_pd,_rz],_rB=[1,_p8,_rA],_rC=[1,_p3,_rB],_rD=[1,_oY,_rC],_rE=[1,_oT,_rD],_rF=[1,_oO,_rE],_rG=[1,_oJ,_rF],_rH=[1,_oE,_rG],_rI=[1,_oA,_rH],_rJ=new T(function(){return B(_o6(_rI));}),_rK=[0,1114111],_rL=[0,34],_rM=[0,39],_rN=function(_rO){var _rP=new T(function(){return B(A(_rO,[_p7]));}),_rQ=new T(function(){return B(A(_rO,[_pc]));}),_rR=new T(function(){return B(A(_rO,[_ph]));}),_rS=new T(function(){return B(A(_rO,[_pm]));}),_rT=new T(function(){return B(A(_rO,[_pr]));}),_rU=new T(function(){return B(A(_rO,[_pw]));}),_rV=new T(function(){return B(A(_rO,[_pB]));});return new F(function(){return _kt([0,function(_rW){switch(E(E(_rW)[1])){case 34:return E(new T(function(){return B(A(_rO,[_rL]));}));case 39:return E(new T(function(){return B(A(_rO,[_rM]));}));case 92:return E(new T(function(){return B(A(_rO,[_nO]));}));case 97:return E(_rP);case 98:return E(_rQ);case 102:return E(_rU);case 110:return E(_rS);case 114:return E(_rV);case 116:return E(_rR);case 118:return E(_rT);default:return [2];}}],new T(function(){return B(_kt([1,B(_lo(_nM,_nP,function(_rX){return [1,B(_lY(_rX,function(_rY){var _rZ=B(_mU(new T(function(){return B(_mK(E(_rX)[1]));}),_mJ,_rY));return !B(_nW(_rZ,_rK))?[2]:B(A(_rO,[new T(function(){var _s0=B(_nT(_rZ));if(_s0>>>0>1114111){var _s1=B(_nR(_s0));}else{var _s1=[0,_s0];}var _s2=_s1,_s3=_s2,_s4=_s3;return _s4;})]));}))];}))],new T(function(){return B(_kt([0,function(_s5){return E(E(_s5)[1])==94?E([0,function(_s6){switch(E(E(_s6)[1])){case 64:return E(new T(function(){return B(A(_rO,[_oD]));}));case 65:return E(new T(function(){return B(A(_rO,[_or]));}));case 66:return E(new T(function(){return B(A(_rO,[_oI]));}));case 67:return E(new T(function(){return B(A(_rO,[_oN]));}));case 68:return E(new T(function(){return B(A(_rO,[_oS]));}));case 69:return E(new T(function(){return B(A(_rO,[_oX]));}));case 70:return E(new T(function(){return B(A(_rO,[_p2]));}));case 71:return E(_rP);case 72:return E(_rQ);case 73:return E(_rR);case 74:return E(_rS);case 75:return E(_rT);case 76:return E(_rU);case 77:return E(_rV);case 78:return E(new T(function(){return B(A(_rO,[_ow]));}));case 79:return E(new T(function(){return B(A(_rO,[_pG]));}));case 80:return E(new T(function(){return B(A(_rO,[_pL]));}));case 81:return E(new T(function(){return B(A(_rO,[_pQ]));}));case 82:return E(new T(function(){return B(A(_rO,[_pV]));}));case 83:return E(new T(function(){return B(A(_rO,[_q0]));}));case 84:return E(new T(function(){return B(A(_rO,[_q5]));}));case 85:return E(new T(function(){return B(A(_rO,[_qa]));}));case 86:return E(new T(function(){return B(A(_rO,[_qf]));}));case 87:return E(new T(function(){return B(A(_rO,[_qk]));}));case 88:return E(new T(function(){return B(A(_rO,[_qp]));}));case 89:return E(new T(function(){return B(A(_rO,[_qu]));}));case 90:return E(new T(function(){return B(A(_rO,[_qz]));}));case 91:return E(new T(function(){return B(A(_rO,[_qE]));}));case 92:return E(new T(function(){return B(A(_rO,[_qJ]));}));case 93:return E(new T(function(){return B(A(_rO,[_qO]));}));case 94:return E(new T(function(){return B(A(_rO,[_qT]));}));case 95:return E(new T(function(){return B(A(_rO,[_qY]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_rJ,[_rO]));})));})));}));});},_s7=function(_s8){return new F(function(){return A(_s8,[_5c]);});},_s9=function(_sa){var _sb=E(_sa);if(!_sb[0]){return E(_s7);}else{var _sc=_sb[2],_sd=E(E(_sb[1])[1]);switch(_sd){case 9:return function(_se){return [0,function(_sf){return E(new T(function(){return B(A(new T(function(){return B(_s9(_sc));}),[_se]));}));}];};case 10:return function(_sg){return [0,function(_sh){return E(new T(function(){return B(A(new T(function(){return B(_s9(_sc));}),[_sg]));}));}];};case 11:return function(_si){return [0,function(_sj){return E(new T(function(){return B(A(new T(function(){return B(_s9(_sc));}),[_si]));}));}];};case 12:return function(_sk){return [0,function(_sl){return E(new T(function(){return B(A(new T(function(){return B(_s9(_sc));}),[_sk]));}));}];};case 13:return function(_sm){return [0,function(_sn){return E(new T(function(){return B(A(new T(function(){return B(_s9(_sc));}),[_sm]));}));}];};case 32:return function(_so){return [0,function(_sp){return E(new T(function(){return B(A(new T(function(){return B(_s9(_sc));}),[_so]));}));}];};case 160:return function(_sq){return [0,function(_sr){return E(new T(function(){return B(A(new T(function(){return B(_s9(_sc));}),[_sq]));}));}];};default:var _ss=u_iswspace(_sd),_st=_ss;return E(_st)==0?E(_s7):function(_su){return [0,function(_sv){return E(new T(function(){return B(A(new T(function(){return B(_s9(_sc));}),[_su]));}));}];};}}},_sw=function(_sx){var _sy=new T(function(){return B(_sw(_sx));}),_sz=[1,function(_sA){return new F(function(){return A(_s9,[_sA,function(_sB){return E([0,function(_sC){return E(E(_sC)[1])==92?E(_sy):[2];}]);}]);});}];return new F(function(){return _kt([0,function(_sD){return E(E(_sD)[1])==92?E([0,function(_sE){var _sF=E(E(_sE)[1]);switch(_sF){case 9:return E(_sz);case 10:return E(_sz);case 11:return E(_sz);case 12:return E(_sz);case 13:return E(_sz);case 32:return E(_sz);case 38:return E(_sy);case 160:return E(_sz);default:var _sG=u_iswspace(_sF),_sH=_sG;return E(_sH)==0?[2]:E(_sz);}}]):[2];}],[0,function(_sI){var _sJ=E(_sI);return E(_sJ[1])==92?E(new T(function(){return B(_rN(function(_sK){return new F(function(){return A(_sx,[[0,_sK,_nG]]);});}));})):B(A(_sx,[[0,_sJ,_1S]]));}]);});},_sL=function(_sM,_sN){return new F(function(){return _sw(function(_sO){var _sP=E(_sO),_sQ=E(_sP[1]);if(E(_sQ[1])==34){if(!E(_sP[2])){return E(new T(function(){return B(A(_sN,[[1,new T(function(){return B(A(_sM,[_9]));})]]));}));}else{return new F(function(){return _sL(function(_sR){return new F(function(){return A(_sM,[[1,_sQ,_sR]]);});},_sN);});}}else{return new F(function(){return _sL(function(_sS){return new F(function(){return A(_sM,[[1,_sQ,_sS]]);});},_sN);});}});});},_sT=new T(function(){return B(unCStr("_\'"));}),_sU=function(_sV){var _sW=u_iswalnum(_sV),_sX=_sW;return E(_sX)==0?B(_86(_if,[0,_sV],_sT)):true;},_sY=function(_sZ){return new F(function(){return _sU(E(_sZ)[1]);});},_t0=new T(function(){return B(unCStr(",;()[]{}`"));}),_t1=new T(function(){return B(unCStr(".."));}),_t2=new T(function(){return B(unCStr("::"));}),_t3=new T(function(){return B(unCStr("->"));}),_t4=[0,64],_t5=[1,_t4,_9],_t6=[0,126],_t7=[1,_t6,_9],_t8=new T(function(){return B(unCStr("=>"));}),_t9=[1,_t8,_9],_ta=[1,_t7,_t9],_tb=[1,_t5,_ta],_tc=[1,_t3,_tb],_td=new T(function(){return B(unCStr("<-"));}),_te=[1,_td,_tc],_tf=[0,124],_tg=[1,_tf,_9],_th=[1,_tg,_te],_ti=[1,_nO,_9],_tj=[1,_ti,_th],_tk=[0,61],_tl=[1,_tk,_9],_tm=[1,_tl,_tj],_tn=[1,_t2,_tm],_to=[1,_t1,_tn],_tp=function(_tq){return new F(function(){return _kt([1,function(_tr){return E(_tr)[0]==0?E(new T(function(){return B(A(_tq,[_lV]));})):[2];}],new T(function(){return B(_kt([0,function(_ts){return E(E(_ts)[1])==39?E([0,function(_tt){var _tu=E(_tt);switch(E(_tu[1])){case 39:return [2];case 92:return E(new T(function(){return B(_rN(function(_tv){return [0,function(_tw){return E(E(_tw)[1])==39?E(new T(function(){return B(A(_tq,[[0,_tv]]));})):[2];}];}));}));default:return [0,function(_tx){return E(E(_tx)[1])==39?E(new T(function(){return B(A(_tq,[[0,_tu]]));})):[2];}];}}]):[2];}],new T(function(){return B(_kt([0,function(_ty){return E(E(_ty)[1])==34?E(new T(function(){return B(_sL(_5q,_tq));})):[2];}],new T(function(){return B(_kt([0,function(_tz){return !B(_86(_if,_tz,_t0))?[2]:B(A(_tq,[[2,[1,_tz,_9]]]));}],new T(function(){return B(_kt([0,function(_tA){return !B(_86(_if,_tA,_nr))?[2]:[1,B(_lK(_ns,function(_tB){var _tC=[1,_tA,_tB];return !B(_86(_7i,_tC,_to))?B(A(_tq,[[4,_tC]])):B(A(_tq,[[2,_tC]]));}))];}],new T(function(){return B(_kt([0,function(_tD){var _tE=E(_tD),_tF=_tE[1],_tG=u_iswalpha(_tF),_tH=_tG;return E(_tH)==0?E(_tF)==95?[1,B(_lK(_sY,function(_tI){return new F(function(){return A(_tq,[[3,[1,_tE,_tI]]]);});}))]:[2]:[1,B(_lK(_sY,function(_tJ){return new F(function(){return A(_tq,[[3,[1,_tE,_tJ]]]);});}))];}],new T(function(){return [1,B(_lo(_nE,_np,_tq))];})));})));})));})));})));}));});},_tK=[0,0],_tL=function(_tM,_tN){return function(_tO){return new F(function(){return A(_s9,[_tO,function(_tP){return E(new T(function(){return B(_tp(function(_tQ){var _tR=E(_tQ);return _tR[0]==2?!B(_l0(_tR[1],_kZ))?[2]:E(new T(function(){return B(A(_tM,[_tK,function(_tS){return [1,function(_tT){return new F(function(){return A(_s9,[_tT,function(_tU){return E(new T(function(){return B(_tp(function(_tV){var _tW=E(_tV);return _tW[0]==2?!B(_l0(_tW[1],_kX))?[2]:E(new T(function(){return B(A(_tN,[_tS]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_tX=function(_tY,_tZ,_u0){var _u1=function(_u2,_u3){return new F(function(){return _kt([1,function(_u4){return new F(function(){return A(_s9,[_u4,function(_u5){return E(new T(function(){return B(_tp(function(_u6){var _u7=E(_u6);if(_u7[0]==4){var _u8=E(_u7[1]);if(!_u8[0]){return new F(function(){return A(_tY,[_u7,_u2,_u3]);});}else{return E(E(_u8[1])[1])==45?E(_u8[2])[0]==0?E([1,function(_u9){return new F(function(){return A(_s9,[_u9,function(_ua){return E(new T(function(){return B(_tp(function(_ub){return new F(function(){return A(_tY,[_ub,_u2,function(_uc){return new F(function(){return A(_u3,[new T(function(){return [0, -E(_uc)[1]];})]);});}]);});}));}));}]);});}]):B(A(_tY,[_u7,_u2,_u3])):B(A(_tY,[_u7,_u2,_u3]));}}else{return new F(function(){return A(_tY,[_u7,_u2,_u3]);});}}));}));}]);});}],new T(function(){return [1,B(_tL(_u1,_u3))];}));});};return new F(function(){return _u1(_tZ,_u0);});},_ud=function(_ue,_uf){return [2];},_ug=function(_uh){var _ui=E(_uh);return _ui[0]==0?[1,new T(function(){return B(_mU(new T(function(){return B(_mK(E(_ui[1])[1]));}),_mJ,_ui[2]));})]:E(_ui[2])[0]==0?E(_ui[3])[0]==0?[1,new T(function(){return B(_mU(_mI,_mJ,_ui[1]));})]:[0]:[0];},_uj=function(_uk){var _ul=E(_uk);if(_ul[0]==5){var _um=B(_ug(_ul[1]));return _um[0]==0?E(_ud):function(_un,_uo){return new F(function(){return A(_uo,[new T(function(){return [0,B(_nT(_um[1]))];})]);});};}else{return E(_ud);}},_up=function(_uq){return [1,function(_ur){return new F(function(){return A(_s9,[_ur,function(_us){return E([3,_uq,_lg]);}]);});}];},_ut=new T(function(){return B(_tX(_uj,_tK,_up));}),_uu=function(_uv){while(1){var _uw=(function(_ux){var _uy=E(_ux);if(!_uy[0]){return [0];}else{var _uz=_uy[2],_uA=E(_uy[1]);if(!E(_uA[2])[0]){return [1,_uA[1],new T(function(){return B(_uu(_uz));})];}else{_uv=_uz;return null;}}})(_uv);if(_uw!=null){return _uw;}}},_uB=function(_uC){var _uD=B(_uu(B(_kj(_ut,_uC))));return _uD[0]==0?E(_kf):E(_uD[2])[0]==0?E(_uD[1]):E(_kh);},_uE=function(_uF,_uG,_uH,_uI,_uJ){var _uK=function(_uL,_uM,_uN){var _uO=function(_uP,_uQ,_uR){return new F(function(){return A(_uN,[[0,_uF,new T(function(){return B(_7X(_uB,_uP));})],_uQ,new T(function(){var _uS=E(E(_uQ)[2]),_uT=E(_uR),_uU=E(_uT[1]),_uV=B(_cD(_uU[1],_uU[2],_uU[3],_uT[2],_uS[1],_uS[2],_uS[3],_9));return [0,E(_uV[1]),_uV[2]];})]);});},_uW=function(_uX){return new F(function(){return _uO(_9,_uL,new T(function(){var _uY=E(E(_uL)[2]),_uZ=E(_uX),_v0=E(_uZ[1]),_v1=B(_cD(_v0[1],_v0[2],_v0[3],_uZ[2],_uY[1],_uY[2],_uY[3],_9));return [0,E(_v1[1]),_v1[2]];},1));});};return new F(function(){return _eD(_jM,_kd,_uL,function(_v2,_v3,_v4){return new F(function(){return A(_uM,[[0,_uF,new T(function(){return B(_7X(_uB,_v2));})],_v3,new T(function(){var _v5=E(E(_v3)[2]),_v6=E(_v4),_v7=E(_v6[1]),_v8=B(_cD(_v7[1],_v7[2],_v7[3],_v6[2],_v5[1],_v5[2],_v5[3],_9));return [0,E(_v8[1]),_v8[2]];})]);});},_uW,_uO,_uW);});};return new F(function(){return _ed(_iz,_uG,function(_v9,_va,_vb){return new F(function(){return _uK(_va,_uH,function(_vc,_vd,_ve){return new F(function(){return A(_uH,[_vc,_vd,new T(function(){return B(_ds(_vb,_ve));})]);});});});},_uI,function(_vf,_vg,_vh){return new F(function(){return _uK(_vg,_uH,function(_vi,_vj,_vk){return new F(function(){return A(_uJ,[_vi,_vj,new T(function(){return B(_ds(_vh,_vk));})]);});});});});});},_vl=new T(function(){return B(unCStr("letter or digit"));}),_vm=[1,_vl,_9],_vn=function(_vo){var _vp=u_iswalnum(E(_vo)[1]),_vq=_vp;return E(_vq)==0?false:true;},_vr=function(_vs,_vt,_vu,_vv,_vw){var _vx=E(_vs),_vy=E(_vx[2]);return new F(function(){return _hN(_fO,_jt,_vn,_vx[1],_vy[1],_vy[2],_vy[3],_vx[3],_vt,_vw);});},_vz=function(_vA,_vB,_vC,_vD,_vE){return new F(function(){return _ja(_vr,_vm,_vA,_vB,_vC,_vD,_vE);});},_vF=function(_vG,_vH,_vI,_vJ,_vK){return new F(function(){return _dA(_vz,_vG,function(_vL,_vM,_vN){return new F(function(){return _uE(_vL,_vM,_vH,_vI,function(_vO,_vP,_vQ){return new F(function(){return A(_vH,[_vO,_vP,new T(function(){return B(_ds(_vN,_vQ));})]);});});});},_vK,function(_vR,_vS,_vT){return new F(function(){return _uE(_vR,_vS,_vH,_vI,function(_vU,_vV,_vW){return new F(function(){return A(_vJ,[_vU,_vV,new T(function(){return B(_ds(_vT,_vW));})]);});});});},_vK);});},_vX=new T(function(){return B(unCStr("SHOW"));}),_vY=[0,_vX,_9],_vZ=function(_w0,_w1,_w2,_w3){var _w4=function(_w5){return new F(function(){return A(_w3,[[0,_w0,_vY],_w1,new T(function(){var _w6=E(E(_w1)[2]),_w7=_w6[1],_w8=_w6[2],_w9=_w6[3],_wa=E(_w5),_wb=E(_wa[1]),_wc=B(_cD(_wb[1],_wb[2],_wb[3],_wa[2],_w7,_w8,_w9,_9)),_wd=E(_wc[1]),_we=B(_cD(_wd[1],_wd[2],_wd[3],_wc[2],_w7,_w8,_w9,_9));return [0,E(_we[1]),_we[2]];})]);});};return new F(function(){return _vF(_w1,function(_wf,_wg,_wh){return new F(function(){return A(_w2,[[0,_w0,_wf],_wg,new T(function(){var _wi=E(E(_wg)[2]),_wj=E(_wh),_wk=E(_wj[1]),_wl=B(_cD(_wk[1],_wk[2],_wk[3],_wj[2],_wi[1],_wi[2],_wi[3],_9));return [0,E(_wl[1]),_wl[2]];})]);});},_w4,function(_wm,_wn,_wo){return new F(function(){return A(_w3,[[0,_w0,_wm],_wn,new T(function(){var _wp=E(E(_wn)[2]),_wq=E(_wo),_wr=E(_wq[1]),_ws=B(_cD(_wr[1],_wr[2],_wr[3],_wq[2],_wp[1],_wp[2],_wp[3],_9));return [0,E(_ws[1]),_ws[2]];})]);});},_w4);});},_wt=new T(function(){return B(unCStr("sS"));}),_wu=new T(function(){return B(_jS(_iq));}),_wv=[0,58],_ww=new T(function(){return B(_jV(_wu,_wv));}),_wx=[1,_vl,_9],_wy=function(_wz,_wA,_wB,_wC,_wD,_wE,_wF,_wG,_wH){var _wI=function(_wJ,_wK){var _wL=new T(function(){var _wM=B(_iP(_wJ,_wK,_wx));return [0,E(_wM[1]),_wM[2]];});return new F(function(){return A(_ww,[[0,_wz,E([0,_wA,_wB,_wC]),E(_wD)],_wE,_wF,function(_wN,_wO,_wP){return new F(function(){return A(_wG,[_wN,_wO,new T(function(){return B(_ds(_wL,_wP));})]);});},function(_wQ){return new F(function(){return A(_wH,[new T(function(){return B(_ds(_wL,_wQ));})]);});}]);});},_wR=E(_wz);if(!_wR[0]){return new F(function(){return _wI([0,_wA,_wB,_wC],_fU);});}else{var _wS=_wR[2],_wT=E(_wR[1]),_wU=_wT[1],_wV=u_iswalnum(_wU),_wW=_wV;if(!E(_wW)){return new F(function(){return _wI([0,_wA,_wB,_wC],[1,[0,E([1,_fR,new T(function(){return B(_hH([1,_wT,_9],_fS));})])],_9]);});}else{switch(E(_wU)){case 9:var _wX=[0,_wA,_wB,(_wC+8|0)-B(_fV(_wC-1|0,8))|0];break;case 10:var _wX=[0,_wA,_wB+1|0,1];break;default:var _wX=[0,_wA,_wB,_wC+1|0];}var _wY=_wX,_wZ=[0,E(_wY),_9],_x0=[0,_wS,E(_wY),E(_wD)];return new F(function(){return A(_wE,[_wT,_x0,_wZ]);});}}},_x1=function(_x2,_x3,_x4,_x5,_x6){var _x7=E(_x2),_x8=E(_x7[2]);return new F(function(){return _wy(_x7[1],_x8[1],_x8[2],_x8[3],_x7[3],_x3,_x4,_x5,_x6);});},_x9=[0,10],_xa=new T(function(){return B(unCStr("lf new-line"));}),_xb=[1,_xa,_9],_xc=function(_xd){return function(_xe,_xf,_xg,_xh,_xi){return new F(function(){return _ja(new T(function(){return B(_jV(_xd,_x9));}),_xb,_xe,_xf,_xg,_xh,_xi);});};},_xj=new T(function(){return B(_xc(_wu));}),_xk=function(_xl,_xm,_xn,_xo,_xp,_xq,_xr){var _xs=function(_xt,_xu,_xv,_xw,_xx,_xy){return new F(function(){return _xz(_xu,function(_xA,_xB,_xC){return new F(function(){return A(_xv,[[1,_xt,_xA],_xB,new T(function(){var _xD=E(E(_xB)[2]),_xE=E(_xC),_xF=E(_xE[1]),_xG=B(_cD(_xF[1],_xF[2],_xF[3],_xE[2],_xD[1],_xD[2],_xD[3],_9));return [0,E(_xG[1]),_xG[2]];})]);});},_xw,function(_xH,_xI,_xJ){return new F(function(){return A(_xx,[[1,_xt,_xH],_xI,new T(function(){var _xK=E(E(_xI)[2]),_xL=E(_xJ),_xM=E(_xL[1]),_xN=B(_cD(_xM[1],_xM[2],_xM[3],_xL[2],_xK[1],_xK[2],_xK[3],_9));return [0,E(_xN[1]),_xN[2]];})]);});},_xy);});},_xz=function(_xO,_xP,_xQ,_xR,_xS){return new F(function(){return A(_xm,[_xO,function(_xT,_xU,_xV){return new F(function(){return A(_xP,[_9,_xU,new T(function(){var _xW=E(E(_xU)[2]),_xX=E(_xV),_xY=E(_xX[1]),_xZ=B(_cD(_xY[1],_xY[2],_xY[3],_xX[2],_xW[1],_xW[2],_xW[3],_9));return [0,E(_xZ[1]),_xZ[2]];})]);});},_xQ,function(_y0,_y1,_y2){return new F(function(){return A(_xR,[_9,_y1,new T(function(){var _y3=E(E(_y1)[2]),_y4=E(_y2),_y5=E(_y4[1]),_y6=B(_cD(_y5[1],_y5[2],_y5[3],_y4[2],_y3[1],_y3[2],_y3[3],_9));return [0,E(_y6[1]),_y6[2]];})]);});},function(_y7){return new F(function(){return A(_xl,[_xO,function(_y8,_y9,_ya){return new F(function(){return _xs(_y8,_y9,_xP,_xQ,function(_yb,_yc,_yd){return new F(function(){return A(_xP,[_yb,_yc,new T(function(){return B(_ds(_ya,_yd));})]);});},function(_ye){return new F(function(){return A(_xQ,[new T(function(){return B(_ds(_ya,_ye));})]);});});});},_xQ,function(_yf,_yg,_yh){return new F(function(){return _xs(_yf,_yg,_xP,_xQ,function(_yi,_yj,_yk){return new F(function(){return A(_xR,[_yi,_yj,new T(function(){var _yl=E(_y7),_ym=E(_yl[1]),_yn=E(_yh),_yo=E(_yn[1]),_yp=E(_yk),_yq=E(_yp[1]),_yr=B(_cD(_yo[1],_yo[2],_yo[3],_yn[2],_yq[1],_yq[2],_yq[3],_yp[2])),_ys=E(_yr[1]),_yt=B(_cD(_ym[1],_ym[2],_ym[3],_yl[2],_ys[1],_ys[2],_ys[3],_yr[2]));return [0,E(_yt[1]),_yt[2]];})]);});},function(_yu){return new F(function(){return A(_xS,[new T(function(){var _yv=E(_y7),_yw=E(_yv[1]),_yx=E(_yh),_yy=E(_yx[1]),_yz=E(_yu),_yA=E(_yz[1]),_yB=B(_cD(_yy[1],_yy[2],_yy[3],_yx[2],_yA[1],_yA[2],_yA[3],_yz[2])),_yC=E(_yB[1]),_yD=B(_cD(_yw[1],_yw[2],_yw[3],_yv[2],_yC[1],_yC[2],_yC[3],_yB[2]));return [0,E(_yD[1]),_yD[2]];})]);});});});},function(_yE){return new F(function(){return A(_xS,[new T(function(){return B(_ds(_y7,_yE));})]);});}]);});}]);});};return new F(function(){return _xz(_xn,_xo,_xp,_xq,_xr);});},_yF=new T(function(){return B(unCStr("tab"));}),_yG=[1,_yF,_9],_yH=[0,9],_yI=function(_yJ){return function(_yK,_yL,_yM,_yN,_yO){return new F(function(){return _ja(new T(function(){return B(_jV(_yJ,_yH));}),_yG,_yK,_yL,_yM,_yN,_yO);});};},_yP=new T(function(){return B(_yI(_wu));}),_yQ=[0,39],_yR=[1,_yQ,_9],_yS=new T(function(){return B(unCStr("\'\\\'\'"));}),_yT=function(_yU){var _yV=E(E(_yU)[1]);return _yV==39?E(_yS):[1,_yQ,new T(function(){return B(_hq(_yV,_yR));})];},_yW=function(_yX,_yY){return [1,_fR,new T(function(){return B(_hH(_yX,[1,_fR,_yY]));})];},_yZ=function(_z0){return new F(function(){return _e(_yS,_z0);});},_z1=function(_z2,_z3){var _z4=E(E(_z3)[1]);return _z4==39?E(_yZ):function(_z5){return [1,_yQ,new T(function(){return B(_hq(_z4,[1,_yQ,_z5]));})];};},_z6=[0,_z1,_yT,_yW],_z7=function(_z8,_z9,_za,_zb,_zc){var _zd=new T(function(){return B(_bm(_z8));}),_ze=function(_zf){return new F(function(){return A(_zb,[_5c,_za,new T(function(){var _zg=E(E(_za)[2]),_zh=E(_zf),_zi=E(_zh[1]),_zj=B(_cD(_zi[1],_zi[2],_zi[3],_zh[2],_zg[1],_zg[2],_zg[3],_9));return [0,E(_zj[1]),_zj[2]];})]);});};return new F(function(){return A(_z9,[_za,function(_zk,_zl,_zm){return new F(function(){return A(_zc,[new T(function(){var _zn=E(E(_zl)[2]),_zo=E(_zm),_zp=E(_zo[1]),_zq=B(_cD(_zp[1],_zp[2],_zp[3],_zo[2],_zn[1],_zn[2],_zn[3],[1,new T(function(){return [1,E(B(A(_zd,[_zk])))];}),_9]));return [0,E(_zq[1]),_zq[2]];})]);});},_ze,function(_zr,_zs,_zt){return new F(function(){return A(_zb,[_5c,_za,new T(function(){var _zu=E(E(_za)[2]),_zv=E(E(_zs)[2]),_zw=E(_zt),_zx=E(_zw[1]),_zy=B(_cD(_zx[1],_zx[2],_zx[3],_zw[2],_zv[1],_zv[2],_zv[3],[1,new T(function(){return [1,E(B(A(_zd,[_zr])))];}),_9])),_zz=E(_zy[1]),_zA=B(_cD(_zz[1],_zz[2],_zz[3],_zy[2],_zu[1],_zu[2],_zu[3],_9));return [0,E(_zA[1]),_zA[2]];})]);});},_ze]);});},_zB=function(_zC,_zD,_zE){return new F(function(){return _z7(_z6,_yP,_zC,function(_zF,_zG,_zH){return new F(function(){return A(_zD,[_5c,_zG,new T(function(){var _zI=E(E(_zG)[2]),_zJ=E(_zH),_zK=E(_zJ[1]),_zL=B(_cD(_zK[1],_zK[2],_zK[3],_zJ[2],_zI[1],_zI[2],_zI[3],_9));return [0,E(_zL[1]),_zL[2]];})]);});},_zE);});},_zM=function(_zN,_zO,_zP,_zQ,_zR){return new F(function(){return A(_xj,[_zN,function(_zS,_zT,_zU){return new F(function(){return _zB(_zT,function(_zV,_zW,_zX){return new F(function(){return A(_zO,[_zV,_zW,new T(function(){return B(_ds(_zU,_zX));})]);});},function(_zY){return new F(function(){return A(_zP,[new T(function(){return B(_ds(_zU,_zY));})]);});});});},_zP,function(_zZ,_A0,_A1){return new F(function(){return _zB(_A0,function(_A2,_A3,_A4){return new F(function(){return A(_zQ,[_A2,_A3,new T(function(){return B(_ds(_A1,_A4));})]);});},function(_A5){return new F(function(){return A(_zR,[new T(function(){return B(_ds(_A1,_A5));})]);});});});},_zR]);});},_A6=[0,E(_9)],_A7=[1,_A6,_9],_A8=function(_A9,_Aa,_Ab,_Ac,_Ad,_Ae,_Af){return new F(function(){return A(_A9,[new T(function(){return B(A(_Aa,[_Ab]));}),function(_Ag){var _Ah=E(_Ag);if(!_Ah[0]){return E(new T(function(){return B(A(_Af,[[0,E(_Ac),_A7]]));}));}else{var _Ai=E(_Ah[1]);return new F(function(){return A(_Ae,[_Ai[1],[0,_Ai[2],E(_Ac),E(_Ad)],[0,E(_Ac),_9]]);});}}]);});},_Aj=new T(function(){return B(unCStr("end of input"));}),_Ak=[1,_Aj,_9],_Al=function(_Am,_An,_Ao,_Ap,_Aq,_Ar,_As,_At){return new F(function(){return _ja(function(_Au,_Av,_Aw,_Ax,_Ay){return new F(function(){return _z7(_Ao,function(_Az,_AA,_AB,_AC,_AD){var _AE=E(_Az);return new F(function(){return _A8(_Am,_An,_AE[1],_AE[2],_AE[3],_AA,_AD);});},_Au,_Ax,_Ay);});},_Ak,_Ap,_Aq,_Ar,_As,_At);});},_AF=function(_AG,_AH,_AI,_AJ,_AK){return new F(function(){return _d0(_xj,_AG,function(_AL,_AM,_AN){return new F(function(){return _Al(_fO,_ix,_z6,_AM,_AH,_AI,function(_AO,_AP,_AQ){return new F(function(){return A(_AH,[_AO,_AP,new T(function(){return B(_ds(_AN,_AQ));})]);});},function(_AR){return new F(function(){return A(_AI,[new T(function(){return B(_ds(_AN,_AR));})]);});});});},_AI,function(_AS,_AT,_AU){return new F(function(){return _Al(_fO,_ix,_z6,_AT,_AH,_AI,function(_AV,_AW,_AX){return new F(function(){return A(_AJ,[_AV,_AW,new T(function(){return B(_ds(_AU,_AX));})]);});},function(_AY){return new F(function(){return A(_AK,[new T(function(){return B(_ds(_AU,_AY));})]);});});});});});},_AZ=function(_B0,_B1,_B2,_B3){var _B4=function(_B5){var _B6=function(_B7){return new F(function(){return A(_B3,[new T(function(){return B(_ds(_B5,_B7));})]);});};return new F(function(){return _zM(_B0,_B1,_B6,function(_B8,_B9,_Ba){return new F(function(){return A(_B2,[_B8,_B9,new T(function(){return B(_ds(_B5,_Ba));})]);});},_B6);});};return new F(function(){return _AF(_B0,_B1,_B4,_B2,_B4);});},_Bb=function(_Bc,_Bd,_Be,_Bf,_Bg){return new F(function(){return _AZ(_Bc,_Bd,_Bf,_Bg);});},_Bh=function(_Bi){return true;},_Bj=function(_Bk,_Bl,_Bm,_Bn,_Bo){var _Bp=E(_Bk),_Bq=E(_Bp[2]);return new F(function(){return _hN(_fO,_ix,_Bh,_Bp[1],_Bq[1],_Bq[2],_Bq[3],_Bp[3],_Bl,_Bo);});},_Br=function(_Bs,_Bt,_Bu,_Bv,_Bw){return new F(function(){return A(_yP,[_Bs,function(_Bx,_By,_Bz){return new F(function(){return _xk(_Bj,_Bb,_By,_Bt,_Bu,function(_BA,_BB,_BC){return new F(function(){return A(_Bt,[_BA,_BB,new T(function(){return B(_ds(_Bz,_BC));})]);});},function(_BD){return new F(function(){return A(_Bu,[new T(function(){return B(_ds(_Bz,_BD));})]);});});});},_Bu,function(_BE,_BF,_BG){return new F(function(){return _xk(_Bj,_Bb,_BF,_Bt,_Bu,function(_BH,_BI,_BJ){return new F(function(){return A(_Bv,[_BH,_BI,new T(function(){return B(_ds(_BG,_BJ));})]);});},function(_BK){return new F(function(){return A(_Bw,[new T(function(){return B(_ds(_BG,_BK));})]);});});});},_Bw]);});},_BL=[0,_vX,_9],_BM=[0,_9,1,1],_BN=function(_BO){return E(_BO);},_BP=function(_BQ){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_BQ));}))));});},_BR=new T(function(){return B(_BP("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_BS=new T(function(){return B(_BP("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_BT=[0,_fO,_BS,_BN,_BR],_BU=function(_BV){return new F(function(){return unAppCStr("string error",new T(function(){return B(_9W(_BV));}));});},_BW=function(_BX,_BY,_BZ,_C0,_C1){return new F(function(){return A(_yP,[_BY,function(_C2,_C3,_C4){return new F(function(){return A(_BZ,[_BX,_C3,new T(function(){var _C5=E(E(_C3)[2]),_C6=E(_C4),_C7=E(_C6[1]),_C8=B(_cD(_C7[1],_C7[2],_C7[3],_C6[2],_C5[1],_C5[2],_C5[3],_9));return [0,E(_C8[1]),_C8[2]];})]);});},_C1,function(_C9,_Ca,_Cb){return new F(function(){return A(_C0,[_BX,_Ca,new T(function(){var _Cc=E(E(_Ca)[2]),_Cd=E(_Cb),_Ce=E(_Cd[1]),_Cf=B(_cD(_Ce[1],_Ce[2],_Ce[3],_Cd[2],_Cc[1],_Cc[2],_Cc[3],_9));return [0,E(_Cf[1]),_Cf[2]];})]);});},_C1]);});},_Cg=function(_Ch,_Ci,_Cj,_Ck,_Cl){return new F(function(){return A(_xj,[_Ch,function(_Cm,_Cn,_Co){return new F(function(){return _BW(_Cm,_Cn,_Ci,function(_Cp,_Cq,_Cr){return new F(function(){return A(_Ci,[_Cp,_Cq,new T(function(){return B(_ds(_Co,_Cr));})]);});},function(_Cs){return new F(function(){return A(_Cj,[new T(function(){return B(_ds(_Co,_Cs));})]);});});});},_Cj,function(_Ct,_Cu,_Cv){return new F(function(){return _BW(_Ct,_Cu,_Ci,function(_Cw,_Cx,_Cy){return new F(function(){return A(_Ck,[_Cw,_Cx,new T(function(){return B(_ds(_Cv,_Cy));})]);});},function(_Cz){return new F(function(){return A(_Cl,[new T(function(){return B(_ds(_Cv,_Cz));})]);});});});},_Cl]);});},_CA=function(_CB,_CC,_CD,_CE,_CF){return new F(function(){return _Cg(_CB,_CC,_CD,_CE,function(_CG){var _CH=E(_CB),_CI=E(_CH[2]),_CJ=E(_CH[1]);return _CJ[0]==0?B(A(_CF,[new T(function(){var _CK=E(_CG),_CL=E(_CK[1]),_CM=B(_cD(_CL[1],_CL[2],_CL[3],_CK[2],_CI[1],_CI[2],_CI[3],_A7));return [0,E(_CM[1]),_CM[2]];})])):B(A(_CC,[_CJ[1],[0,_CJ[2],E(_CI),E(_CH[3])],[0,E(_CI),_9]]));});});},_CN=function(_CO,_CP,_CQ,_CR,_CS){return new F(function(){return _d0(_CA,_CO,_CP,_CQ,_CR);});},_CT=function(_CU,_CV,_CW){return [0,_CU,E(E(_CV)),_CW];},_CX=function(_CY,_CZ,_D0){var _D1=new T(function(){return B(_ir(_CY));}),_D2=new T(function(){return B(_ir(_CY));});return new F(function(){return A(_CZ,[_D0,function(_D3,_D4,_D5){return new F(function(){return A(_D1,[[0,new T(function(){return B(A(_D2,[new T(function(){return B(_CT(_D3,_D4,_D5));})]));})]]);});},function(_D6){return new F(function(){return A(_D1,[[0,new T(function(){return B(A(_D2,[[1,_D6]]));})]]);});},function(_D7,_D8,_D9){return new F(function(){return A(_D1,[new T(function(){return [1,E(B(A(_D2,[new T(function(){return B(_CT(_D7,_D8,_D9));})])))];})]);});},function(_Da){return new F(function(){return A(_D1,[new T(function(){return [1,E(B(A(_D2,[[1,_Da]])))];})]);});}]);});},_Db=function(_Dc){return function(_Dd,_De,_Df,_Dg,_Dh){return new F(function(){return A(_Dg,[new T(function(){var _Di=B(_CX(_BT,_Dj,[0,new T(function(){var _Dk=B(_CX(_BT,_CN,[0,_Dc,E(_BM),E(_5c)]));if(!_Dk[0]){var _Dl=E(_Dk[1]),_Dm=_Dl[0]==0?E(_Dl[1]):B(_BU(_Dl[1]));}else{var _Dn=E(_Dk[1]),_Dm=_Dn[0]==0?E(_Dn[1]):B(_BU(_Dn[1]));}return _Dm;}),E(_BM),E(_5c)]));if(!_Di[0]){var _Do=E(_Di[1]),_Dp=_Do[0]==0?E(_Do[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_Do[1]));})));})],_9],_9],_BL];}else{var _Dq=E(_Di[1]),_Dp=_Dq[0]==0?E(_Dq[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_Dq[1]));})));})],_9],_9],_BL];}return _Dp;}),_Dd,new T(function(){return [0,E(E(_Dd)[2]),_9];})]);});};},_Dr=function(_Ds,_Dt,_Du,_Dv,_Dw){return new F(function(){return _Br(_Ds,function(_Dx,_Dy,_Dz){return new F(function(){return A(_Db,[_Dx,_Dy,_Dt,_Du,function(_DA,_DB,_DC){return new F(function(){return A(_Dt,[_DA,_DB,new T(function(){return B(_ds(_Dz,_DC));})]);});},function(_DD){return new F(function(){return A(_Du,[new T(function(){return B(_ds(_Dz,_DD));})]);});}]);});},_Du,function(_DE,_DF,_DG){return new F(function(){return A(_Db,[_DE,_DF,_Dt,_Du,function(_DH,_DI,_DJ){return new F(function(){return A(_Dv,[_DH,_DI,new T(function(){return B(_ds(_DG,_DJ));})]);});},function(_DK){return new F(function(){return A(_Dw,[new T(function(){return B(_ds(_DG,_DK));})]);});}]);});},_Dw);});},_DL=function(_DM,_DN,_DO,_DP,_DQ,_DR){var _DS=function(_DT,_DU,_DV,_DW,_DX){var _DY=function(_DZ,_E0,_E1,_E2,_E3){return new F(function(){return A(_DW,[[0,[1,[0,_DM,_E0,_E1]],_DZ],_E2,new T(function(){var _E4=E(_E3),_E5=E(_E4[1]),_E6=E(E(_E2)[2]),_E7=B(_cD(_E5[1],_E5[2],_E5[3],_E4[2],_E6[1],_E6[2],_E6[3],_9));return [0,E(_E7[1]),_E7[2]];})]);});},_E8=function(_E9){return new F(function(){return _DY(_9,_vX,_9,_DT,new T(function(){var _Ea=E(E(_DT)[2]),_Eb=E(_E9),_Ec=E(_Eb[1]),_Ed=B(_cD(_Ec[1],_Ec[2],_Ec[3],_Eb[2],_Ea[1],_Ea[2],_Ea[3],_9));return [0,E(_Ed[1]),_Ed[2]];}));});};return new F(function(){return _Dr(_DT,function(_Ee,_Ef,_Eg){var _Eh=E(_Ee),_Ei=E(_Eh[2]);return new F(function(){return A(_DU,[[0,[1,[0,_DM,_Ei[1],_Ei[2]]],_Eh[1]],_Ef,new T(function(){var _Ej=E(_Eg),_Ek=E(_Ej[1]),_El=E(E(_Ef)[2]),_Em=B(_cD(_Ek[1],_Ek[2],_Ek[3],_Ej[2],_El[1],_El[2],_El[3],_9));return [0,E(_Em[1]),_Em[2]];})]);});},_E8,function(_En,_Eo,_Ep){var _Eq=E(_En),_Er=E(_Eq[2]);return new F(function(){return _DY(_Eq[1],_Er[1],_Er[2],_Eo,_Ep);});},_E8);});};return new F(function(){return A(_xj,[_DN,function(_Es,_Et,_Eu){return new F(function(){return _DS(_Et,_DO,_DP,function(_Ev,_Ew,_Ex){return new F(function(){return A(_DO,[_Ev,_Ew,new T(function(){return B(_ds(_Eu,_Ex));})]);});},function(_Ey){return new F(function(){return A(_DP,[new T(function(){return B(_ds(_Eu,_Ey));})]);});});});},_DP,function(_Ez,_EA,_EB){return new F(function(){return _DS(_EA,_DO,_DP,function(_EC,_ED,_EE){return new F(function(){return A(_DQ,[_EC,_ED,new T(function(){return B(_ds(_EB,_EE));})]);});},function(_EF){return new F(function(){return A(_DR,[new T(function(){return B(_ds(_EB,_EF));})]);});});});},_DR]);});},_EG=new T(function(){return B(unCStr(" associative operator"));}),_EH=function(_EI,_EJ){var _EK=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_e(_EI,_EG));}))))];}),_9];return function(_EL,_EM,_EN,_EO,_EP){return new F(function(){return A(_EJ,[_EL,function(_EQ,_ER,_ES){return new F(function(){return A(_EP,[new T(function(){var _ET=E(E(_ER)[2]),_EU=E(_ES),_EV=E(_EU[1]),_EW=B(_cD(_EV[1],_EV[2],_EV[3],_EU[2],_ET[1],_ET[2],_ET[3],_EK));return [0,E(_EW[1]),_EW[2]];})]);});},_EP,function(_EX,_EY,_EZ){return new F(function(){return A(_EP,[new T(function(){var _F0=E(E(_EY)[2]),_F1=E(_EZ),_F2=E(_F1[1]),_F3=B(_cD(_F2[1],_F2[2],_F2[3],_F1[2],_F0[1],_F0[2],_F0[3],_EK));return [0,E(_F3[1]),_F3[2]];})]);});},_EP]);});};},_F4=function(_F5,_F6,_F7,_F8,_F9,_Fa){var _Fb=E(_F5);if(!_Fb[0]){return new F(function(){return A(_Fa,[new T(function(){return [0,E(E(_F6)[2]),_9];})]);});}else{return new F(function(){return A(_Fb[1],[_F6,_F7,_F8,_F9,function(_Fc){return new F(function(){return _F4(_Fb[2],_F6,_F7,_F8,function(_Fd,_Fe,_Ff){return new F(function(){return A(_F9,[_Fd,_Fe,new T(function(){return B(_ds(_Fc,_Ff));})]);});},function(_Fg){return new F(function(){return A(_Fa,[new T(function(){return B(_ds(_Fc,_Fg));})]);});});});}]);});}},_Fh=new T(function(){return B(unCStr("right"));}),_Fi=new T(function(){return B(unCStr("left"));}),_Fj=new T(function(){return B(unCStr("non"));}),_Fk=new T(function(){return B(unCStr("operator"));}),_Fl=[1,_Fk,_9],_Fm=[1,_9,_9],_Fn=function(_Fo){var _Fp=E(_Fo);if(!_Fp[0]){return [0,_9,_9,_9,_9,_9];}else{var _Fq=_Fp[2],_Fr=E(_Fp[1]);switch(_Fr[0]){case 0:var _Fs=_Fr[1],_Ft=B(_Fn(_Fq)),_Fu=_Ft[1],_Fv=_Ft[2],_Fw=_Ft[3],_Fx=_Ft[4],_Fy=_Ft[5];switch(E(_Fr[2])){case 0:return [0,_Fu,_Fv,[1,_Fs,_Fw],_Fx,_Fy];case 1:return [0,_Fu,[1,_Fs,_Fv],_Fw,_Fx,_Fy];default:return [0,[1,_Fs,_Fu],_Fv,_Fw,_Fx,_Fy];}break;case 1:var _Fz=B(_Fn(_Fq));return [0,_Fz[1],_Fz[2],_Fz[3],[1,_Fr[1],_Fz[4]],_Fz[5]];default:var _FA=B(_Fn(_Fq));return [0,_FA[1],_FA[2],_FA[3],_FA[4],[1,_Fr[1],_FA[5]]];}}},_FB=function(_FC,_FD){while(1){var _FE=(function(_FF,_FG){var _FH=E(_FG);if(!_FH[0]){return E(_FF);}else{var _FI=new T(function(){var _FJ=B(_Fn(_FH[1]));return [0,_FJ[1],_FJ[2],_FJ[3],_FJ[4],_FJ[5]];}),_FK=new T(function(){return E(E(_FI)[2]);}),_FL=new T(function(){return B(_EH(_Fi,function(_FM,_FN,_FO,_FP,_FQ){return new F(function(){return _F4(_FK,_FM,_FN,_FO,_FP,_FQ);});}));}),_FR=new T(function(){return E(E(_FI)[1]);}),_FS=new T(function(){return E(E(_FI)[3]);}),_FT=new T(function(){return B(_EH(_Fj,function(_FU,_FV,_FW,_FX,_FY){return new F(function(){return _F4(_FS,_FU,_FV,_FW,_FX,_FY);});}));}),_FZ=function(_G0,_G1,_G2,_G3,_G4,_G5){var _G6=function(_G7,_G8,_G9,_Ga,_Gb){var _Gc=new T(function(){return B(A(_G0,[_G7]));});return new F(function(){return _F4(new T(function(){return E(E(_FI)[5]);}),_G8,function(_Gd,_Ge,_Gf){return new F(function(){return A(_G9,[new T(function(){return B(A(_Gd,[_Gc]));}),_Ge,new T(function(){var _Gg=E(E(_Ge)[2]),_Gh=E(_Gf),_Gi=E(_Gh[1]),_Gj=B(_cD(_Gi[1],_Gi[2],_Gi[3],_Gh[2],_Gg[1],_Gg[2],_Gg[3],_9));return [0,E(_Gj[1]),_Gj[2]];})]);});},_Ga,function(_Gk,_Gl,_Gm){return new F(function(){return A(_Gb,[new T(function(){return B(A(_Gk,[_Gc]));}),_Gl,new T(function(){var _Gn=E(E(_Gl)[2]),_Go=_Gn[1],_Gp=_Gn[2],_Gq=_Gn[3],_Gr=E(_Gm),_Gs=E(_Gr[1]),_Gt=_Gs[2],_Gu=_Gs[3],_Gv=E(_Gr[2]);if(!_Gv[0]){switch(B(_cv(_Gs[1],_Go))){case 0:var _Gw=[0,E(_Gn),_9];break;case 1:if(_Gt>=_Gp){if(_Gt!=_Gp){var _Gx=[0,E(_Gs),_9];}else{if(_Gu>=_Gq){var _Gy=_Gu!=_Gq?[0,E(_Gs),_9]:[0,E(_Gs),_cC];}else{var _Gy=[0,E(_Gn),_9];}var _Gz=_Gy,_Gx=_Gz;}var _GA=_Gx,_GB=_GA;}else{var _GB=[0,E(_Gn),_9];}var _GC=_GB,_Gw=_GC;break;default:var _Gw=[0,E(_Gs),_9];}var _GD=_Gw;}else{var _GE=B(_iP(_Gs,_Gv,_Fm)),_GF=E(_GE[1]),_GG=B(_cD(_GF[1],_GF[2],_GF[3],_GE[2],_Go,_Gp,_Gq,_9)),_GD=[0,E(_GG[1]),_GG[2]];}var _GH=_GD,_GI=_GH,_GJ=_GI,_GK=_GJ;return _GK;})]);});},function(_GL){return new F(function(){return A(_Gb,[_Gc,_G8,new T(function(){var _GM=E(E(_G8)[2]),_GN=_GM[1],_GO=_GM[2],_GP=_GM[3],_GQ=E(_GL),_GR=B(_iP(_GQ[1],_GQ[2],_Fm)),_GS=E(_GR[1]),_GT=B(_cD(_GS[1],_GS[2],_GS[3],_GR[2],_GN,_GO,_GP,_9)),_GU=E(_GT[1]),_GV=B(_cD(_GU[1],_GU[2],_GU[3],_GT[2],_GN,_GO,_GP,_9));return [0,E(_GV[1]),_GV[2]];})]);});});});};return new F(function(){return A(_FF,[_G1,function(_GW,_GX,_GY){return new F(function(){return _G6(_GW,_GX,_G2,_G3,function(_GZ,_H0,_H1){return new F(function(){return A(_G2,[_GZ,_H0,new T(function(){return B(_ds(_GY,_H1));})]);});});});},_G3,function(_H2,_H3,_H4){return new F(function(){return _G6(_H2,_H3,_G2,_G3,function(_H5,_H6,_H7){return new F(function(){return A(_G4,[_H5,_H6,new T(function(){return B(_ds(_H4,_H7));})]);});});});},_G5]);});},_H8=function(_H9,_Ha,_Hb,_Hc,_Hd){var _He=function(_Hf,_Hg,_Hh){return new F(function(){return _FZ(_Hf,_Hg,_Ha,_Hb,function(_Hi,_Hj,_Hk){return new F(function(){return A(_Hc,[_Hi,_Hj,new T(function(){return B(_ds(_Hh,_Hk));})]);});},function(_Hl){return new F(function(){return A(_Hd,[new T(function(){return B(_ds(_Hh,_Hl));})]);});});});};return new F(function(){return _F4(new T(function(){return E(E(_FI)[4]);}),_H9,function(_Hm,_Hn,_Ho){return new F(function(){return _FZ(_Hm,_Hn,_Ha,_Hb,function(_Hp,_Hq,_Hr){return new F(function(){return A(_Ha,[_Hp,_Hq,new T(function(){return B(_ds(_Ho,_Hr));})]);});},function(_Hs){return new F(function(){return A(_Hb,[new T(function(){return B(_ds(_Ho,_Hs));})]);});});});},_Hb,function(_Ht,_Hu,_Hv){return new F(function(){return _He(_Ht,_Hu,new T(function(){var _Hw=E(_Hv),_Hx=E(_Hw[2]);if(!_Hx[0]){var _Hy=E(_Hw);}else{var _Hz=B(_iP(_Hw[1],_Hx,_Fm)),_Hy=[0,E(_Hz[1]),_Hz[2]];}var _HA=_Hy;return _HA;}));});},function(_HB){return new F(function(){return _He(_5q,_H9,new T(function(){var _HC=E(E(_H9)[2]),_HD=E(_HB),_HE=B(_iP(_HD[1],_HD[2],_Fm)),_HF=E(_HE[1]),_HG=B(_cD(_HF[1],_HF[2],_HF[3],_HE[2],_HC[1],_HC[2],_HC[3],_9));return [0,E(_HG[1]),_HG[2]];}));});});});},_HH=function(_HI,_HJ,_HK,_HL,_HM,_HN){var _HO=function(_HP){return new F(function(){return A(_FL,[_HJ,_HK,_HL,function(_HQ,_HR,_HS){return new F(function(){return A(_HM,[_HQ,_HR,new T(function(){return B(_ds(_HP,_HS));})]);});},function(_HT){return new F(function(){return A(_FT,[_HJ,_HK,_HL,function(_HU,_HV,_HW){return new F(function(){return A(_HM,[_HU,_HV,new T(function(){var _HX=E(_HP),_HY=E(_HX[1]),_HZ=E(_HT),_I0=E(_HZ[1]),_I1=E(_HW),_I2=E(_I1[1]),_I3=B(_cD(_I0[1],_I0[2],_I0[3],_HZ[2],_I2[1],_I2[2],_I2[3],_I1[2])),_I4=E(_I3[1]),_I5=B(_cD(_HY[1],_HY[2],_HY[3],_HX[2],_I4[1],_I4[2],_I4[3],_I3[2]));return [0,E(_I5[1]),_I5[2]];})]);});},function(_I6){return new F(function(){return A(_HN,[new T(function(){var _I7=E(_HP),_I8=E(_I7[1]),_I9=E(_HT),_Ia=E(_I9[1]),_Ib=E(_I6),_Ic=E(_Ib[1]),_Id=B(_cD(_Ia[1],_Ia[2],_Ia[3],_I9[2],_Ic[1],_Ic[2],_Ic[3],_Ib[2])),_Ie=E(_Id[1]),_If=B(_cD(_I8[1],_I8[2],_I8[3],_I7[2],_Ie[1],_Ie[2],_Ie[3],_Id[2]));return [0,E(_If[1]),_If[2]];})]);});}]);});}]);});},_Ig=function(_Ih,_Ii,_Ij,_Ik,_Il,_Im){var _In=function(_Io,_Ip,_Iq){return new F(function(){return A(_Ij,[new T(function(){return B(A(_Ih,[_HI,_Io]));}),_Ip,new T(function(){var _Ir=E(E(_Ip)[2]),_Is=E(_Iq),_It=E(_Is[1]),_Iu=B(_cD(_It[1],_It[2],_It[3],_Is[2],_Ir[1],_Ir[2],_Ir[3],_9));return [0,E(_Iu[1]),_Iu[2]];})]);});};return new F(function(){return _H8(_Ii,function(_Iv,_Iw,_Ix){return new F(function(){return _HH(_Iv,_Iw,_In,_Ik,function(_Iy,_Iz,_IA){return new F(function(){return _In(_Iy,_Iz,new T(function(){var _IB=E(_Ix),_IC=E(_IB[1]),_ID=E(_IA),_IE=E(_ID[1]),_IF=B(_cD(_IC[1],_IC[2],_IC[3],_IB[2],_IE[1],_IE[2],_IE[3],_ID[2]));return [0,E(_IF[1]),_IF[2]];},1));});},function(_IG){return new F(function(){return _In(_Iv,_Iw,new T(function(){var _IH=E(E(_Iw)[2]),_II=E(_Ix),_IJ=E(_II[1]),_IK=E(_IG),_IL=E(_IK[1]),_IM=B(_cD(_IL[1],_IL[2],_IL[3],_IK[2],_IH[1],_IH[2],_IH[3],_9)),_IN=E(_IM[1]),_IO=B(_cD(_IJ[1],_IJ[2],_IJ[3],_II[2],_IN[1],_IN[2],_IN[3],_IM[2]));return [0,E(_IO[1]),_IO[2]];},1));});});});},_Ik,function(_IP,_IQ,_IR){var _IS=function(_IT,_IU,_IV){return new F(function(){return A(_Il,[new T(function(){return B(A(_Ih,[_HI,_IT]));}),_IU,new T(function(){var _IW=E(E(_IU)[2]),_IX=E(_IR),_IY=E(_IX[1]),_IZ=E(_IV),_J0=E(_IZ[1]),_J1=B(_cD(_IY[1],_IY[2],_IY[3],_IX[2],_J0[1],_J0[2],_J0[3],_IZ[2])),_J2=E(_J1[1]),_J3=B(_cD(_J2[1],_J2[2],_J2[3],_J1[2],_IW[1],_IW[2],_IW[3],_9));return [0,E(_J3[1]),_J3[2]];})]);});};return new F(function(){return _HH(_IP,_IQ,_In,_Ik,_IS,function(_J4){return new F(function(){return _IS(_IP,_IQ,new T(function(){var _J5=E(E(_IQ)[2]),_J6=E(_J4),_J7=E(_J6[1]),_J8=B(_cD(_J7[1],_J7[2],_J7[3],_J6[2],_J5[1],_J5[2],_J5[3],_9));return [0,E(_J8[1]),_J8[2]];},1));});});});},_Im);});};return new F(function(){return _F4(_FR,_HJ,function(_J9,_Ja,_Jb){return new F(function(){return _Ig(_J9,_Ja,_HK,_HL,function(_Jc,_Jd,_Je){return new F(function(){return A(_HK,[_Jc,_Jd,new T(function(){return B(_ds(_Jb,_Je));})]);});},function(_Jf){return new F(function(){return A(_HL,[new T(function(){return B(_ds(_Jb,_Jf));})]);});});});},_HL,function(_Jg,_Jh,_Ji){return new F(function(){return _Ig(_Jg,_Jh,_HK,_HL,function(_Jj,_Jk,_Jl){return new F(function(){return A(_HM,[_Jj,_Jk,new T(function(){return B(_ds(_Ji,_Jl));})]);});},function(_Jm){return new F(function(){return _HO(new T(function(){return B(_ds(_Ji,_Jm));}));});});});},_HO);});},_Jn=new T(function(){return B(_EH(_Fh,function(_Jo,_Jp,_Jq,_Jr,_Js){return new F(function(){return _F4(_FR,_Jo,_Jp,_Jq,_Jr,_Js);});}));}),_Jt=function(_Ju,_Jv,_Jw,_Jx,_Jy,_Jz){var _JA=function(_JB){return new F(function(){return A(_Jn,[_Jv,_Jw,_Jx,function(_JC,_JD,_JE){return new F(function(){return A(_Jy,[_JC,_JD,new T(function(){return B(_ds(_JB,_JE));})]);});},function(_JF){return new F(function(){return A(_FT,[_Jv,_Jw,_Jx,function(_JG,_JH,_JI){return new F(function(){return A(_Jy,[_JG,_JH,new T(function(){var _JJ=E(_JB),_JK=E(_JJ[1]),_JL=E(_JF),_JM=E(_JL[1]),_JN=E(_JI),_JO=E(_JN[1]),_JP=B(_cD(_JM[1],_JM[2],_JM[3],_JL[2],_JO[1],_JO[2],_JO[3],_JN[2])),_JQ=E(_JP[1]),_JR=B(_cD(_JK[1],_JK[2],_JK[3],_JJ[2],_JQ[1],_JQ[2],_JQ[3],_JP[2]));return [0,E(_JR[1]),_JR[2]];})]);});},function(_JS){return new F(function(){return A(_Jz,[new T(function(){var _JT=E(_JB),_JU=E(_JT[1]),_JV=E(_JF),_JW=E(_JV[1]),_JX=E(_JS),_JY=E(_JX[1]),_JZ=B(_cD(_JW[1],_JW[2],_JW[3],_JV[2],_JY[1],_JY[2],_JY[3],_JX[2])),_K0=E(_JZ[1]),_K1=B(_cD(_JU[1],_JU[2],_JU[3],_JT[2],_K0[1],_K0[2],_K0[3],_JZ[2]));return [0,E(_K1[1]),_K1[2]];})]);});}]);});}]);});},_K2=function(_K3,_K4,_K5,_K6,_K7,_K8){var _K9=function(_Ka){var _Kb=new T(function(){return B(A(_K3,[_Ju,_Ka]));});return function(_Kc,_Kd,_Ke,_Kf,_Kg){return new F(function(){return _Jt(_Kb,_Kc,_Kd,_Ke,_Kf,function(_Kh){return new F(function(){return A(_Kf,[_Kb,_Kc,new T(function(){var _Ki=E(E(_Kc)[2]),_Kj=E(_Kh),_Kk=E(_Kj[1]),_Kl=B(_cD(_Kk[1],_Kk[2],_Kk[3],_Kj[2],_Ki[1],_Ki[2],_Ki[3],_9));return [0,E(_Kl[1]),_Kl[2]];})]);});});});};};return new F(function(){return _H8(_K4,function(_Km,_Kn,_Ko){return new F(function(){return A(_K9,[_Km,_Kn,_K5,_K6,function(_Kp,_Kq,_Kr){return new F(function(){return A(_K5,[_Kp,_Kq,new T(function(){return B(_ds(_Ko,_Kr));})]);});},function(_Ks){return new F(function(){return A(_K6,[new T(function(){return B(_ds(_Ko,_Ks));})]);});}]);});},_K6,function(_Kt,_Ku,_Kv){return new F(function(){return A(_K9,[_Kt,_Ku,_K5,_K6,function(_Kw,_Kx,_Ky){return new F(function(){return A(_K7,[_Kw,_Kx,new T(function(){return B(_ds(_Kv,_Ky));})]);});},function(_Kz){return new F(function(){return A(_K8,[new T(function(){return B(_ds(_Kv,_Kz));})]);});}]);});},_K8);});};return new F(function(){return _F4(_FK,_Jv,function(_KA,_KB,_KC){return new F(function(){return _K2(_KA,_KB,_Jw,_Jx,function(_KD,_KE,_KF){return new F(function(){return A(_Jw,[_KD,_KE,new T(function(){return B(_ds(_KC,_KF));})]);});},function(_KG){return new F(function(){return A(_Jx,[new T(function(){return B(_ds(_KC,_KG));})]);});});});},_Jx,function(_KH,_KI,_KJ){return new F(function(){return _K2(_KH,_KI,_Jw,_Jx,function(_KK,_KL,_KM){return new F(function(){return A(_Jy,[_KK,_KL,new T(function(){return B(_ds(_KJ,_KM));})]);});},function(_KN){return new F(function(){return _JA(new T(function(){return B(_ds(_KJ,_KN));}));});});});},_JA);});},_KO=function(_KP,_KQ,_KR,_KS,_KT,_KU){var _KV=function(_KW,_KX,_KY,_KZ,_L0,_L1){var _L2=function(_L3){return function(_L4,_L5,_L6,_L7,_L8){return new F(function(){return A(_Jn,[_L4,_L5,_L6,_L7,function(_L9){return new F(function(){return A(_FL,[_L4,_L5,_L6,function(_La,_Lb,_Lc){return new F(function(){return A(_L7,[_La,_Lb,new T(function(){return B(_ds(_L9,_Lc));})]);});},function(_Ld){return new F(function(){return A(_FT,[_L4,_L5,_L6,function(_Le,_Lf,_Lg){return new F(function(){return A(_L7,[_Le,_Lf,new T(function(){var _Lh=E(_L9),_Li=E(_Lh[1]),_Lj=E(_Ld),_Lk=E(_Lj[1]),_Ll=E(_Lg),_Lm=E(_Ll[1]),_Ln=B(_cD(_Lk[1],_Lk[2],_Lk[3],_Lj[2],_Lm[1],_Lm[2],_Lm[3],_Ll[2])),_Lo=E(_Ln[1]),_Lp=B(_cD(_Li[1],_Li[2],_Li[3],_Lh[2],_Lo[1],_Lo[2],_Lo[3],_Ln[2]));return [0,E(_Lp[1]),_Lp[2]];})]);});},function(_Lq){return new F(function(){return A(_L7,[new T(function(){return B(A(_KW,[_KP,_L3]));}),_L4,new T(function(){var _Lr=E(E(_L4)[2]),_Ls=E(_L9),_Lt=E(_Ls[1]),_Lu=E(_Ld),_Lv=E(_Lu[1]),_Lw=E(_Lq),_Lx=E(_Lw[1]),_Ly=B(_cD(_Lx[1],_Lx[2],_Lx[3],_Lw[2],_Lr[1],_Lr[2],_Lr[3],_9)),_Lz=E(_Ly[1]),_LA=B(_cD(_Lv[1],_Lv[2],_Lv[3],_Lu[2],_Lz[1],_Lz[2],_Lz[3],_Ly[2])),_LB=E(_LA[1]),_LC=B(_cD(_Lt[1],_Lt[2],_Lt[3],_Ls[2],_LB[1],_LB[2],_LB[3],_LA[2]));return [0,E(_LC[1]),_LC[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _H8(_KX,function(_LD,_LE,_LF){return new F(function(){return A(_L2,[_LD,_LE,_KY,_KZ,function(_LG,_LH,_LI){return new F(function(){return A(_KY,[_LG,_LH,new T(function(){return B(_ds(_LF,_LI));})]);});},function(_LJ){return new F(function(){return A(_KZ,[new T(function(){return B(_ds(_LF,_LJ));})]);});}]);});},_KZ,function(_LK,_LL,_LM){return new F(function(){return A(_L2,[_LK,_LL,_KY,_KZ,function(_LN,_LO,_LP){return new F(function(){return A(_L0,[_LN,_LO,new T(function(){return B(_ds(_LM,_LP));})]);});},function(_LQ){return new F(function(){return A(_L1,[new T(function(){return B(_ds(_LM,_LQ));})]);});}]);});},_L1);});};return new F(function(){return _ja(function(_LR,_LS,_LT,_LU,_LV){return new F(function(){return _HH(_KP,_LR,_LS,_LT,_LU,function(_LW){return new F(function(){return _Jt(_KP,_LR,_LS,_LT,function(_LX,_LY,_LZ){return new F(function(){return A(_LU,[_LX,_LY,new T(function(){return B(_ds(_LW,_LZ));})]);});},function(_M0){var _M1=function(_M2){return new F(function(){return A(_LU,[_KP,_LR,new T(function(){var _M3=E(E(_LR)[2]),_M4=E(_LW),_M5=E(_M4[1]),_M6=E(_M0),_M7=E(_M6[1]),_M8=E(_M2),_M9=E(_M8[1]),_Ma=B(_cD(_M9[1],_M9[2],_M9[3],_M8[2],_M3[1],_M3[2],_M3[3],_9)),_Mb=E(_Ma[1]),_Mc=B(_cD(_M7[1],_M7[2],_M7[3],_M6[2],_Mb[1],_Mb[2],_Mb[3],_Ma[2])),_Md=E(_Mc[1]),_Me=B(_cD(_M5[1],_M5[2],_M5[3],_M4[2],_Md[1],_Md[2],_Md[3],_Mc[2]));return [0,E(_Me[1]),_Me[2]];})]);});};return new F(function(){return _F4(_FS,_LR,function(_Mf,_Mg,_Mh){return new F(function(){return _KV(_Mf,_Mg,_LS,_LT,function(_Mi,_Mj,_Mk){return new F(function(){return A(_LS,[_Mi,_Mj,new T(function(){return B(_ds(_Mh,_Mk));})]);});},function(_Ml){return new F(function(){return A(_LT,[new T(function(){return B(_ds(_Mh,_Ml));})]);});});});},_LT,function(_Mm,_Mn,_Mo){return new F(function(){return _KV(_Mm,_Mn,_LS,_LT,function(_Mp,_Mq,_Mr){return new F(function(){return A(_LU,[_Mp,_Mq,new T(function(){var _Ms=E(_LW),_Mt=E(_Ms[1]),_Mu=E(_M0),_Mv=E(_Mu[1]),_Mw=E(_Mo),_Mx=E(_Mw[1]),_My=E(_Mr),_Mz=E(_My[1]),_MA=B(_cD(_Mx[1],_Mx[2],_Mx[3],_Mw[2],_Mz[1],_Mz[2],_Mz[3],_My[2])),_MB=E(_MA[1]),_MC=B(_cD(_Mv[1],_Mv[2],_Mv[3],_Mu[2],_MB[1],_MB[2],_MB[3],_MA[2])),_MD=E(_MC[1]),_ME=B(_cD(_Mt[1],_Mt[2],_Mt[3],_Ms[2],_MD[1],_MD[2],_MD[3],_MC[2]));return [0,E(_ME[1]),_ME[2]];})]);});},function(_MF){return new F(function(){return _M1(new T(function(){var _MG=E(_Mo),_MH=E(_MG[1]),_MI=E(_MF),_MJ=E(_MI[1]),_MK=B(_cD(_MH[1],_MH[2],_MH[3],_MG[2],_MJ[1],_MJ[2],_MJ[3],_MI[2]));return [0,E(_MK[1]),_MK[2]];},1));});});});},_M1);});});});});});},_Fl,_KQ,_KR,_KS,_KT,_KU);});};_FC=function(_ML,_MM,_MN,_MO,_MP){return new F(function(){return _H8(_ML,function(_MQ,_MR,_MS){return new F(function(){return _KO(_MQ,_MR,_MM,_MN,function(_MT,_MU,_MV){return new F(function(){return A(_MM,[_MT,_MU,new T(function(){return B(_ds(_MS,_MV));})]);});},function(_MW){return new F(function(){return A(_MN,[new T(function(){return B(_ds(_MS,_MW));})]);});});});},_MN,function(_MX,_MY,_MZ){return new F(function(){return _KO(_MX,_MY,_MM,_MN,function(_N0,_N1,_N2){return new F(function(){return A(_MO,[_N0,_N1,new T(function(){return B(_ds(_MZ,_N2));})]);});},function(_N3){return new F(function(){return A(_MP,[new T(function(){return B(_ds(_MZ,_N3));})]);});});});},_MP);});};_FD=_FH[2];return null;}})(_FC,_FD);if(_FE!=null){return _FE;}}},_N4=0,_N5=[3,_],_N6=function(_N7,_N8){return [5,_N5,_N7,_N8];},_N9=new T(function(){return B(unCStr("=>"));}),_Na=function(_Nb){return E(E(_Nb)[1]);},_Nc=function(_Nd,_Ne,_Nf,_Ng){while(1){var _Nh=E(_Ng);if(!_Nh[0]){return [0,_Nd,_Ne,_Nf];}else{var _Ni=_Nh[2];switch(E(E(_Nh[1])[1])){case 9:var _Nj=(_Nf+8|0)-B(_fV(_Nf-1|0,8))|0;_Ng=_Ni;_Nf=_Nj;continue;case 10:var _Nk=_Ne+1|0;_Nf=1;_Ng=_Ni;_Ne=_Nk;continue;default:var _Nj=_Nf+1|0;_Ng=_Ni;_Nf=_Nj;continue;}}}},_Nl=function(_Nm){return E(E(_Nm)[1]);},_Nn=function(_No){return E(E(_No)[2]);},_Np=function(_Nq){return [0,E(E(_Nq)[2]),_9];},_Nr=function(_Ns,_Nt,_Nu,_Nv,_Nw,_Nx,_Ny){var _Nz=E(_Nt);if(!_Nz[0]){return new F(function(){return A(_Nx,[_9,_Nu,new T(function(){return B(_Np(_Nu));})]);});}else{var _NA=E(_Nu),_NB=E(_NA[2]),_NC=new T(function(){return B(_Na(_Ns));}),_ND=[0,E(_NB),[1,[2,E([1,_fR,new T(function(){return B(_hH(_Nz,_fS));})])],_fU]],_NE=[2,E([1,_fR,new T(function(){return B(_hH(_Nz,_fS));})])],_NF=new T(function(){var _NG=B(_Nc(_NB[1],_NB[2],_NB[3],_Nz));return [0,_NG[1],_NG[2],_NG[3]];}),_NH=function(_NI,_NJ){var _NK=E(_NI);if(!_NK[0]){return new F(function(){return A(_Nv,[_Nz,new T(function(){return [0,_NJ,E(E(_NF)),E(_NA[3])];}),new T(function(){return [0,E(E(_NF)),_9];})]);});}else{return new F(function(){return A(new T(function(){return B(_Nl(_NC));}),[new T(function(){return B(A(new T(function(){return B(_Nn(_Ns));}),[_NJ]));}),function(_NL){var _NM=E(_NL);if(!_NM[0]){return E(new T(function(){return B(A(_Nw,[_ND]));}));}else{var _NN=E(_NM[1]),_NO=E(_NN[1]);return E(_NK[1])[1]!=_NO[1]?B(A(_Nw,[[0,E(_NB),[1,_NE,[1,[0,E([1,_fR,new T(function(){return B(_hH([1,_NO,_9],_fS));})])],_9]]]])):B(_NH(_NK[2],_NN[2]));}}]);});}};return new F(function(){return A(_Nl,[_NC,new T(function(){return B(A(_Nn,[_Ns,_NA[1]]));}),function(_NP){var _NQ=E(_NP);if(!_NQ[0]){return E(new T(function(){return B(A(_Ny,[_ND]));}));}else{var _NR=E(_NQ[1]),_NS=E(_NR[1]);return E(_Nz[1])[1]!=_NS[1]?B(A(_Ny,[[0,E(_NB),[1,_NE,[1,[0,E([1,_fR,new T(function(){return B(_hH([1,_NS,_9],_fS));})])],_9]]]])):B(_NH(_Nz[2],_NR[2]));}}]);});}},_NT=function(_NU,_NV,_NW,_NX,_NY){return new F(function(){return _Nr(_jU,_N9,_NU,function(_NZ,_O0,_O1){return new F(function(){return A(_NV,[_N6,_O0,new T(function(){var _O2=E(E(_O0)[2]),_O3=E(_O1),_O4=E(_O3[1]),_O5=B(_cD(_O4[1],_O4[2],_O4[3],_O3[2],_O2[1],_O2[2],_O2[3],_9));return [0,E(_O5[1]),_O5[2]];})]);});},_NW,function(_O6,_O7,_O8){return new F(function(){return A(_NX,[_N6,_O7,new T(function(){var _O9=E(E(_O7)[2]),_Oa=E(_O8),_Ob=E(_Oa[1]),_Oc=B(_cD(_Ob[1],_Ob[2],_Ob[3],_Oa[2],_O9[1],_O9[2],_O9[3],_9));return [0,E(_Oc[1]),_Oc[2]];})]);});},_NY);});},_Od=[0,_NT,_N4],_Oe=[1,_Od,_9],_Of=[1,_Oe,_9],_Og=1,_Oh=[2,_],_Oi=function(_N7,_N8){return [5,_Oh,_N7,_N8];},_Oj=new T(function(){return B(unCStr("\\/"));}),_Ok=function(_Ol,_Om,_On,_Oo,_Op){return new F(function(){return _Nr(_jU,_Oj,_Ol,function(_Oq,_Or,_Os){return new F(function(){return A(_Om,[_Oi,_Or,new T(function(){var _Ot=E(E(_Or)[2]),_Ou=E(_Os),_Ov=E(_Ou[1]),_Ow=B(_cD(_Ov[1],_Ov[2],_Ov[3],_Ou[2],_Ot[1],_Ot[2],_Ot[3],_9));return [0,E(_Ow[1]),_Ow[2]];})]);});},_On,function(_Ox,_Oy,_Oz){return new F(function(){return A(_Oo,[_Oi,_Oy,new T(function(){var _OA=E(E(_Oy)[2]),_OB=E(_Oz),_OC=E(_OB[1]),_OD=B(_cD(_OC[1],_OC[2],_OC[3],_OB[2],_OA[1],_OA[2],_OA[3],_9));return [0,E(_OD[1]),_OD[2]];})]);});},_Op);});},_OE=[0,_Ok,_Og],_OF=[1,_],_OG=function(_N7,_N8){return [5,_OF,_N7,_N8];},_OH=new T(function(){return B(unCStr("/\\"));}),_OI=function(_OJ,_OK,_OL,_OM,_ON){return new F(function(){return _Nr(_jU,_OH,_OJ,function(_OO,_OP,_OQ){return new F(function(){return A(_OK,[_OG,_OP,new T(function(){var _OR=E(E(_OP)[2]),_OS=E(_OQ),_OT=E(_OS[1]),_OU=B(_cD(_OT[1],_OT[2],_OT[3],_OS[2],_OR[1],_OR[2],_OR[3],_9));return [0,E(_OU[1]),_OU[2]];})]);});},_OL,function(_OV,_OW,_OX){return new F(function(){return A(_OM,[_OG,_OW,new T(function(){var _OY=E(E(_OW)[2]),_OZ=E(_OX),_P0=E(_OZ[1]),_P1=B(_cD(_P0[1],_P0[2],_P0[3],_OZ[2],_OY[1],_OY[2],_OY[3],_9));return [0,E(_P1[1]),_P1[2]];})]);});},_ON);});},_P2=[0,_OI,_Og],_P3=[1,_P2,_9],_P4=[1,_OE,_P3],_P5=[1,_P4,_Of],_P6=[0,_],_P7=function(_N8){return [4,_P6,_N8];},_P8=[0,45],_P9=[1,_P8,_9],_Pa=function(_Pb,_Pc,_Pd,_Pe,_Pf){return new F(function(){return _Nr(_jU,_P9,_Pb,function(_Pg,_Ph,_Pi){return new F(function(){return A(_Pc,[_P7,_Ph,new T(function(){var _Pj=E(E(_Ph)[2]),_Pk=E(_Pi),_Pl=E(_Pk[1]),_Pm=B(_cD(_Pl[1],_Pl[2],_Pl[3],_Pk[2],_Pj[1],_Pj[2],_Pj[3],_9));return [0,E(_Pm[1]),_Pm[2]];})]);});},_Pd,function(_Pn,_Po,_Pp){return new F(function(){return A(_Pe,[_P7,_Po,new T(function(){var _Pq=E(E(_Po)[2]),_Pr=E(_Pp),_Ps=E(_Pr[1]),_Pt=B(_cD(_Ps[1],_Ps[2],_Ps[3],_Pr[2],_Pq[1],_Pq[2],_Pq[3],_9));return [0,E(_Pt[1]),_Pt[2]];})]);});},_Pf);});},_Pu=[1,_Pa],_Pv=[1,_Pu,_9],_Pw=[1,_Pv,_P5],_Px=new T(function(){return B(unCStr("number"));}),_Py=[1,_Px,_9],_Pz=new T(function(){return B(err(_kg));}),_PA=new T(function(){return B(err(_ke));}),_PB=new T(function(){return B(_tX(_uj,_tK,_up));}),_PC=function(_PD){return function(_PE,_PF,_PG,_PH,_PI){return new F(function(){return A(_PH,[new T(function(){var _PJ=B(_uu(B(_kj(_PB,_PD))));return _PJ[0]==0?E(_PA):E(_PJ[2])[0]==0?E(_PJ[1]):E(_Pz);}),_PE,new T(function(){return [0,E(E(_PE)[2]),_9];})]);});};},_PK=function(_PL,_PM,_PN,_PO,_PP){return new F(function(){return _dA(_jG,_PL,function(_PQ,_PR,_PS){return new F(function(){return A(_PC,[_PQ,_PR,_PM,_PN,function(_PT,_PU,_PV){return new F(function(){return A(_PM,[_PT,_PU,new T(function(){return B(_ds(_PS,_PV));})]);});},function(_PW){return new F(function(){return A(_PN,[new T(function(){return B(_ds(_PS,_PW));})]);});}]);});},_PN,function(_PX,_PY,_PZ){return new F(function(){return A(_PC,[_PX,_PY,_PM,_PN,function(_Q0,_Q1,_Q2){return new F(function(){return A(_PO,[_Q0,_Q1,new T(function(){return B(_ds(_PZ,_Q2));})]);});},function(_Q3){return new F(function(){return A(_PP,[new T(function(){return B(_ds(_PZ,_Q3));})]);});}]);});},_PP);});},_Q4=function(_Q5,_Q6,_Q7,_Q8,_Q9){return new F(function(){return _PK(_Q5,function(_Qa,_Qb,_Qc){return new F(function(){return A(_Q6,[[1,[0,_,_Qa]],_Qb,new T(function(){var _Qd=E(E(_Qb)[2]),_Qe=E(_Qc),_Qf=E(_Qe[1]),_Qg=B(_cD(_Qf[1],_Qf[2],_Qf[3],_Qe[2],_Qd[1],_Qd[2],_Qd[3],_9));return [0,E(_Qg[1]),_Qg[2]];})]);});},_Q7,function(_Qh,_Qi,_Qj){return new F(function(){return A(_Q8,[[1,[0,_,_Qh]],_Qi,new T(function(){var _Qk=E(E(_Qi)[2]),_Ql=_Qk[1],_Qm=_Qk[2],_Qn=_Qk[3],_Qo=E(_Qj),_Qp=E(_Qo[1]),_Qq=_Qp[2],_Qr=_Qp[3],_Qs=E(_Qo[2]);if(!_Qs[0]){switch(B(_cv(_Qp[1],_Ql))){case 0:var _Qt=[0,E(_Qk),_9];break;case 1:if(_Qq>=_Qm){if(_Qq!=_Qm){var _Qu=[0,E(_Qp),_9];}else{if(_Qr>=_Qn){var _Qv=_Qr!=_Qn?[0,E(_Qp),_9]:[0,E(_Qp),_cC];}else{var _Qv=[0,E(_Qk),_9];}var _Qw=_Qv,_Qu=_Qw;}var _Qx=_Qu,_Qy=_Qx;}else{var _Qy=[0,E(_Qk),_9];}var _Qz=_Qy,_Qt=_Qz;break;default:var _Qt=[0,E(_Qp),_9];}var _QA=_Qt;}else{var _QB=B(_iP(_Qp,_Qs,_Py)),_QC=E(_QB[1]),_QD=B(_cD(_QC[1],_QC[2],_QC[3],_QB[2],_Ql,_Qm,_Qn,_9)),_QA=[0,E(_QD[1]),_QD[2]];}var _QE=_QA,_QF=_QE,_QG=_QF,_QH=_QG;return _QH;})]);});},function(_QI){return new F(function(){return A(_Q9,[new T(function(){var _QJ=E(_QI),_QK=B(_iP(_QJ[1],_QJ[2],_Py));return [0,E(_QK[1]),_QK[2]];})]);});});});},_QL=new T(function(){return B(unCStr("P_"));}),_QM=function(_QN,_QO,_QP,_QQ,_QR){return new F(function(){return _Nr(_jU,_QL,_QN,function(_QS,_QT,_QU){return new F(function(){return _Q4(_QT,_QO,_QP,function(_QV,_QW,_QX){return new F(function(){return A(_QO,[_QV,_QW,new T(function(){return B(_ds(_QU,_QX));})]);});},function(_QY){return new F(function(){return A(_QP,[new T(function(){return B(_ds(_QU,_QY));})]);});});});},_QP,function(_QZ,_R0,_R1){return new F(function(){return _Q4(_R0,_QO,_QP,function(_R2,_R3,_R4){return new F(function(){return A(_QQ,[_R2,_R3,new T(function(){return B(_ds(_R1,_R4));})]);});},function(_R5){return new F(function(){return A(_QR,[new T(function(){return B(_ds(_R1,_R5));})]);});});});},_QR);});},_R6=[0,41],_R7=new T(function(){return B(_jV(_jU,_R6));}),_R8=function(_R9,_Ra,_Rb,_Rc,_Rd,_Re){return new F(function(){return A(_R7,[_Ra,function(_Rf,_Rg,_Rh){return new F(function(){return A(_Rb,[_R9,_Rg,new T(function(){var _Ri=E(E(_Rg)[2]),_Rj=E(_Rh),_Rk=E(_Rj[1]),_Rl=B(_cD(_Rk[1],_Rk[2],_Rk[3],_Rj[2],_Ri[1],_Ri[2],_Ri[3],_9));return [0,E(_Rl[1]),_Rl[2]];})]);});},_Rc,function(_Rm,_Rn,_Ro){return new F(function(){return A(_Rd,[_R9,_Rn,new T(function(){var _Rp=E(E(_Rn)[2]),_Rq=E(_Ro),_Rr=E(_Rq[1]),_Rs=B(_cD(_Rr[1],_Rr[2],_Rr[3],_Rq[2],_Rp[1],_Rp[2],_Rp[3],_9));return [0,E(_Rs[1]),_Rs[2]];})]);});},_Re]);});},_Rt=function(_Ru,_Rv,_Rw,_Rx,_Ry){return new F(function(){return A(_Rz,[_Ru,function(_RA,_RB,_RC){return new F(function(){return _R8(_RA,_RB,_Rv,_Rw,function(_RD,_RE,_RF){return new F(function(){return A(_Rv,[_RD,_RE,new T(function(){return B(_ds(_RC,_RF));})]);});},function(_RG){return new F(function(){return A(_Rw,[new T(function(){return B(_ds(_RC,_RG));})]);});});});},_Rw,function(_RH,_RI,_RJ){return new F(function(){return _R8(_RH,_RI,_Rv,_Rw,function(_RK,_RL,_RM){return new F(function(){return A(_Rx,[_RK,_RL,new T(function(){return B(_ds(_RJ,_RM));})]);});},function(_RN){return new F(function(){return A(_Ry,[new T(function(){return B(_ds(_RJ,_RN));})]);});});});},_Ry]);});},_RO=[0,40],_RP=new T(function(){return B(_jV(_jU,_RO));}),_RQ=function(_RR,_RS,_RT,_RU,_RV){var _RW=function(_RX){return new F(function(){return _QM(_RR,_RS,_RT,function(_RY,_RZ,_S0){return new F(function(){return A(_RU,[_RY,_RZ,new T(function(){return B(_ds(_RX,_S0));})]);});},function(_S1){return new F(function(){return A(_RV,[new T(function(){return B(_ds(_RX,_S1));})]);});});});};return new F(function(){return A(_RP,[_RR,function(_S2,_S3,_S4){return new F(function(){return _Rt(_S3,_RS,_RT,function(_S5,_S6,_S7){return new F(function(){return A(_RS,[_S5,_S6,new T(function(){return B(_ds(_S4,_S7));})]);});},function(_S8){return new F(function(){return A(_RT,[new T(function(){return B(_ds(_S4,_S8));})]);});});});},_RT,function(_S9,_Sa,_Sb){return new F(function(){return _Rt(_Sa,_RS,_RT,function(_Sc,_Sd,_Se){return new F(function(){return A(_RU,[_Sc,_Sd,new T(function(){return B(_ds(_Sb,_Se));})]);});},function(_Sf){return new F(function(){return _RW(new T(function(){return B(_ds(_Sb,_Sf));}));});});});},_RW]);});},_Rz=new T(function(){return B(_FB(_RQ,_Pw));}),_Sg=function(_Sh,_Si,_Sj,_Sk,_Sl){return new F(function(){return A(_Rz,[_Sh,function(_Sm,_Sn,_So){return new F(function(){return _DL(_Sm,_Sn,_Si,_Sj,function(_Sp,_Sq,_Sr){return new F(function(){return A(_Si,[_Sp,_Sq,new T(function(){return B(_ds(_So,_Sr));})]);});},function(_Ss){return new F(function(){return A(_Sj,[new T(function(){return B(_ds(_So,_Ss));})]);});});});},_Sj,function(_St,_Su,_Sv){return new F(function(){return _DL(_St,_Su,_Si,_Sj,function(_Sw,_Sx,_Sy){return new F(function(){return A(_Sk,[_Sw,_Sx,new T(function(){return B(_ds(_Sv,_Sy));})]);});},function(_Sz){return new F(function(){return A(_Sl,[new T(function(){return B(_ds(_Sv,_Sz));})]);});});});},_Sl]);});},_SA=function(_SB,_SC,_SD,_SE,_SF){return new F(function(){return _ed(_iz,_SB,function(_SG,_SH,_SI){return new F(function(){return _Sg(_SH,_SC,_SD,function(_SJ,_SK,_SL){return new F(function(){return A(_SC,[_SJ,_SK,new T(function(){return B(_ds(_SI,_SL));})]);});},function(_SM){return new F(function(){return A(_SD,[new T(function(){return B(_ds(_SI,_SM));})]);});});});},_SD,function(_SN,_SO,_SP){return new F(function(){return _Sg(_SO,_SC,_SD,function(_SQ,_SR,_SS){return new F(function(){return A(_SE,[_SQ,_SR,new T(function(){return B(_ds(_SP,_SS));})]);});},function(_ST){return new F(function(){return A(_SF,[new T(function(){return B(_ds(_SP,_ST));})]);});});});});});},_SU=function(_SV,_SW,_SX,_SY,_SZ,_T0,_T1,_T2){var _T3=E(_SV);if(!_T3[0]){return new F(function(){return A(_T2,[[0,E([0,_SW,_SX,_SY]),_fU]]);});}else{var _T4=_T3[1];if(!B(_86(_if,_T4,_wt))){return new F(function(){return A(_T2,[[0,E([0,_SW,_SX,_SY]),[1,[0,E([1,_fR,new T(function(){return B(_hH([1,_T4,_9],_fS));})])],_9]]]);});}else{var _T5=function(_T6,_T7,_T8,_T9){var _Ta=[0,E([0,_T6,_T7,_T8]),_9],_Tb=[0,E([0,_T6,_T7,_T8]),_cC];return new F(function(){return _ed(_x1,[0,_T3[2],E(_T9),E(_SZ)],function(_Tc,_Td,_Te){return new F(function(){return _SA(_Td,_T0,_T1,function(_Tf,_Tg,_Th){return new F(function(){return A(_T0,[_Tf,_Tg,new T(function(){return B(_ds(_Te,_Th));})]);});},function(_Ti){return new F(function(){return A(_T1,[new T(function(){return B(_ds(_Te,_Ti));})]);});});});},_T1,function(_Tj,_Tk,_Tl){return new F(function(){return _SA(_Tk,_T0,_T1,function(_Tm,_Tn,_To){return new F(function(){return A(_T0,[_Tm,_Tn,new T(function(){var _Tp=E(_Tl),_Tq=E(_Tp[1]),_Tr=E(_To),_Ts=E(_Tr[1]),_Tt=B(_cD(_Tq[1],_Tq[2],_Tq[3],_Tp[2],_Ts[1],_Ts[2],_Ts[3],_Tr[2])),_Tu=E(_Tt[1]),_Tv=_Tu[2],_Tw=_Tu[3],_Tx=E(_Tt[2]);if(!_Tx[0]){switch(B(_cv(_T6,_Tu[1]))){case 0:var _Ty=[0,E(_Tu),_9];break;case 1:if(_T7>=_Tv){if(_T7!=_Tv){var _Tz=E(_Ta);}else{if(_T8>=_Tw){var _TA=_T8!=_Tw?E(_Ta):E(_Tb);}else{var _TA=[0,E(_Tu),_9];}var _TB=_TA,_Tz=_TB;}var _TC=_Tz,_TD=_TC;}else{var _TD=[0,E(_Tu),_9];}var _TE=_TD,_Ty=_TE;break;default:var _Ty=E(_Ta);}var _TF=_Ty;}else{var _TF=[0,E(_Tu),_Tx];}var _TG=_TF,_TH=_TG,_TI=_TH,_TJ=_TI,_TK=_TJ,_TL=_TK;return _TL;})]);});},function(_TM){return new F(function(){return A(_T1,[new T(function(){var _TN=E(_Tl),_TO=E(_TN[1]),_TP=E(_TM),_TQ=E(_TP[1]),_TR=B(_cD(_TO[1],_TO[2],_TO[3],_TN[2],_TQ[1],_TQ[2],_TQ[3],_TP[2])),_TS=E(_TR[1]),_TT=_TS[2],_TU=_TS[3],_TV=E(_TR[2]);if(!_TV[0]){switch(B(_cv(_T6,_TS[1]))){case 0:var _TW=[0,E(_TS),_9];break;case 1:if(_T7>=_TT){if(_T7!=_TT){var _TX=E(_Ta);}else{if(_T8>=_TU){var _TY=_T8!=_TU?E(_Ta):E(_Tb);}else{var _TY=[0,E(_TS),_9];}var _TZ=_TY,_TX=_TZ;}var _U0=_TX,_U1=_U0;}else{var _U1=[0,E(_TS),_9];}var _U2=_U1,_TW=_U2;break;default:var _TW=E(_Ta);}var _U3=_TW;}else{var _U3=[0,E(_TS),_TV];}var _U4=_U3,_U5=_U4,_U6=_U5,_U7=_U6,_U8=_U7,_U9=_U8;return _U9;})]);});});});});});};switch(E(E(_T4)[1])){case 9:var _Ua=(_SY+8|0)-B(_fV(_SY-1|0,8))|0;return new F(function(){return _T5(_SW,_SX,_Ua,[0,_SW,_SX,_Ua]);});break;case 10:var _Ub=_SX+1|0;return new F(function(){return _T5(_SW,_Ub,1,[0,_SW,_Ub,1]);});break;default:var _Uc=_SY+1|0;return new F(function(){return _T5(_SW,_SX,_Uc,[0,_SW,_SX,_Uc]);});}}}},_Ud=function(_Ue,_Uf){return E(_1);},_Ug=function(_Uh,_Ui,_Uj,_Uk){var _Ul=E(_Uj);switch(_Ul[0]){case 0:var _Um=E(_Uk);return _Um[0]==0?E(_1):E(_Um[1]);case 1:return new F(function(){return A(_Uh,[_Ul[1],_9]);});break;case 2:return new F(function(){return A(_Ui,[_Ul[1],[1,new T(function(){return B(_Ug(_Uh,_Ui,_Ul[2],_Uk));}),_9]]);});break;default:return new F(function(){return A(_Ui,[_Ul[1],[1,new T(function(){return B(_Ug(_Uh,_Ui,_Ul[2],_Uk));}),[1,new T(function(){return B(_Ug(_Uh,_Ui,_Ul[3],_Uk));}),_9]]]);});}},_Un=function(_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uu,_Uv){var _Uw=E(_Uu);switch(_Uw[0]){case 0:return [0];case 1:return new F(function(){return A(_Ur,[_Uw[1],_9]);});break;case 2:return new F(function(){return A(_Uo,[_Uw[1],[1,new T(function(){return B(_Ug(_Ur,_Us,_Uw[2],_Uv));}),_9]]);});break;case 3:return new F(function(){return A(_Uo,[_Uw[1],[1,new T(function(){return B(_Ug(_Ur,_Us,_Uw[2],_Uv));}),[1,new T(function(){return B(_Ug(_Ur,_Us,_Uw[3],_Uv));}),_9]]]);});break;case 4:return new F(function(){return A(_Up,[_Uw[1],[1,new T(function(){return B(_Un(_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uw[2],_Uv));}),_9]]);});break;case 5:return new F(function(){return A(_Up,[_Uw[1],[1,new T(function(){return B(_Un(_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uw[2],_Uv));}),[1,new T(function(){return B(_Un(_Uo,_Up,_Uq,_Ur,_Us,_Ut,_Uw[3],_Uv));}),_9]]]);});break;default:var _Ux=_Uw[1],_Uy=_Uw[2];return new F(function(){return A(_Uq,[_Ux,[1,new T(function(){return B(A(_Ut,[new T(function(){return B(A(_Uy,[_ae]));}),_Ux]));}),[1,new T(function(){return B(_Un(_Uo,_Up,_Uq,_Ur,_Us,_Ut,B(A(_Uy,[_ae])),[1,new T(function(){return B(A(_Ut,[new T(function(){return B(A(_Uy,[_ae]));}),_Ux]));}),_9]));}),_9]]]);});}},_Uz=[0,95],_UA=[1,_Uz,_9],_UB=[1,_UA,_9],_UC=function(_UD){var _UE=function(_UF){var _UG=E(new T(function(){var _UH=B(_CX(_BT,_Rz,[0,_UD,E(_BM),E(_5c)]));if(!_UH[0]){var _UI=E(_UH[1]),_UJ=_UI[0]==0?[1,_UI[1]]:[0,_UI[1]];}else{var _UK=E(_UH[1]),_UJ=_UK[0]==0?[1,_UK[1]]:[0,_UK[1]];}return _UJ;}));return _UG[0]==0?function(_UL,_UM,_UN,_UO,_UP){return new F(function(){return A(_UO,[[0,[0,new T(function(){var _UQ=E(_UG[1]),_UR=E(_UQ[1]);return B(_9R(_UR[1],_UR[2],_UR[3],_UQ[2]));})],_9],_UL,new T(function(){return [0,E(E(_UL)[2]),_9];})]);});}:function(_US,_UT,_UU,_UV,_UW){return new F(function(){return A(_UV,[[0,[0,new T(function(){return B(_Un(_Q,_u,_Q,_N,_Q,_Ud,_UG[1],_UB));})],_9],_US,new T(function(){return [0,E(E(_US)[2]),_9];})]);});};};return function(_UX,_UY,_UZ,_V0,_V1){return new F(function(){return A(_xj,[_UX,function(_V2,_V3,_V4){return new F(function(){return A(_UE,[_,_V3,_UY,_UZ,function(_V5,_V6,_V7){return new F(function(){return A(_UY,[_V5,_V6,new T(function(){return B(_ds(_V4,_V7));})]);});},function(_V8){return new F(function(){return A(_UZ,[new T(function(){return B(_ds(_V4,_V8));})]);});}]);});},_UZ,function(_V9,_Va,_Vb){return new F(function(){return A(_UE,[_,_Va,_UY,_UZ,function(_Vc,_Vd,_Ve){return new F(function(){return A(_V0,[_Vc,_Vd,new T(function(){return B(_ds(_Vb,_Ve));})]);});},function(_Vf){return new F(function(){return A(_V1,[new T(function(){return B(_ds(_Vb,_Vf));})]);});}]);});},_V1]);});};},_Vg=function(_Vh,_Vi,_Vj,_Vk,_Vl,_Vm,_Vn,_Vo,_Vp,_Vq){return new F(function(){return _hN(_Vh,_Vi,function(_Vr){return !B(_86(_if,_Vr,_Vj))?true:false;},_Vk,_Vl,_Vm,_Vn,_Vo,_Vp,_Vq);});},_Vs=[0,9],_Vt=[1,_Vs,_9],_Vu=[0,10],_Vv=[1,_Vu,_Vt],_Vw=function(_Vx,_Vy,_Vz,_VA,_VB){var _VC=E(_Vx),_VD=E(_VC[2]);return new F(function(){return _Vg(_fO,_ix,_Vv,_VC[1],_VD[1],_VD[2],_VD[3],_VC[3],_Vy,_VB);});},_VE=function(_VF,_VG,_VH,_VI,_VJ){return new F(function(){return _dA(_Vw,_VF,function(_VK,_VL,_VM){return new F(function(){return A(_UC,[_VK,_VL,_VG,_VH,function(_VN,_VO,_VP){return new F(function(){return A(_VG,[_VN,_VO,new T(function(){return B(_ds(_VM,_VP));})]);});},function(_VQ){return new F(function(){return A(_VH,[new T(function(){return B(_ds(_VM,_VQ));})]);});}]);});},_VH,function(_VR,_VS,_VT){return new F(function(){return A(_UC,[_VR,_VS,_VG,_VH,function(_VU,_VV,_VW){return new F(function(){return A(_VI,[_VU,_VV,new T(function(){return B(_ds(_VT,_VW));})]);});},function(_VX){return new F(function(){return A(_VJ,[new T(function(){return B(_ds(_VT,_VX));})]);});}]);});},_VJ);});},_VY=function(_VZ,_W0,_W1,_W2,_W3,_W4){var _W5=function(_W6,_W7,_W8,_W9,_Wa,_Wb){var _Wc=function(_Wd){var _We=[0,[1,[0,_VZ,_W6,new T(function(){return B(_7X(_uB,_Wd));})]],_9];return function(_Wf,_Wg,_Wh,_Wi,_Wj){return new F(function(){return A(_xj,[_Wf,function(_Wk,_Wl,_Wm){return new F(function(){return A(_Wg,[_We,_Wl,new T(function(){var _Wn=E(E(_Wl)[2]),_Wo=E(_Wm),_Wp=E(_Wo[1]),_Wq=B(_cD(_Wp[1],_Wp[2],_Wp[3],_Wo[2],_Wn[1],_Wn[2],_Wn[3],_9));return [0,E(_Wq[1]),_Wq[2]];})]);});},_Wh,function(_Wr,_Ws,_Wt){return new F(function(){return A(_Wi,[_We,_Ws,new T(function(){var _Wu=E(E(_Ws)[2]),_Wv=E(_Wt),_Ww=E(_Wv[1]),_Wx=B(_cD(_Ww[1],_Ww[2],_Ww[3],_Wv[2],_Wu[1],_Wu[2],_Wu[3],_9));return [0,E(_Wx[1]),_Wx[2]];})]);});},_Wj]);});};},_Wy=function(_Wz,_WA,_WB,_WC,_WD){var _WE=function(_WF,_WG,_WH){return new F(function(){return A(_Wc,[_WF,_WG,_WA,_WB,function(_WI,_WJ,_WK){return new F(function(){return A(_WC,[_WI,_WJ,new T(function(){return B(_ds(_WH,_WK));})]);});},function(_WL){return new F(function(){return A(_WD,[new T(function(){return B(_ds(_WH,_WL));})]);});}]);});},_WM=function(_WN){return new F(function(){return _WE(_9,_Wz,new T(function(){var _WO=E(E(_Wz)[2]),_WP=E(_WN),_WQ=E(_WP[1]),_WR=B(_cD(_WQ[1],_WQ[2],_WQ[3],_WP[2],_WO[1],_WO[2],_WO[3],_9));return [0,E(_WR[1]),_WR[2]];}));});};return new F(function(){return _eD(_jM,_kd,_Wz,function(_WS,_WT,_WU){return new F(function(){return A(_Wc,[_WS,_WT,_WA,_WB,function(_WV,_WW,_WX){return new F(function(){return A(_WA,[_WV,_WW,new T(function(){return B(_ds(_WU,_WX));})]);});},function(_WY){return new F(function(){return A(_WB,[new T(function(){return B(_ds(_WU,_WY));})]);});}]);});},_WM,_WE,_WM);});};return new F(function(){return _ed(_iz,_W7,function(_WZ,_X0,_X1){return new F(function(){return _Wy(_X0,_W8,_W9,function(_X2,_X3,_X4){return new F(function(){return A(_W8,[_X2,_X3,new T(function(){return B(_ds(_X1,_X4));})]);});},function(_X5){return new F(function(){return A(_W9,[new T(function(){return B(_ds(_X1,_X5));})]);});});});},_W9,function(_X6,_X7,_X8){return new F(function(){return _Wy(_X7,_W8,_W9,function(_X9,_Xa,_Xb){return new F(function(){return A(_Wa,[_X9,_Xa,new T(function(){return B(_ds(_X8,_Xb));})]);});},function(_Xc){return new F(function(){return A(_Wb,[new T(function(){return B(_ds(_X8,_Xc));})]);});});});});});},_Xd=function(_Xe,_Xf,_Xg,_Xh,_Xi){return new F(function(){return _dA(_vz,_Xe,function(_Xj,_Xk,_Xl){return new F(function(){return _W5(_Xj,_Xk,_Xf,_Xg,function(_Xm,_Xn,_Xo){return new F(function(){return A(_Xf,[_Xm,_Xn,new T(function(){return B(_ds(_Xl,_Xo));})]);});},function(_Xp){return new F(function(){return A(_Xg,[new T(function(){return B(_ds(_Xl,_Xp));})]);});});});},_Xi,function(_Xq,_Xr,_Xs){return new F(function(){return _W5(_Xq,_Xr,_Xf,_Xg,function(_Xt,_Xu,_Xv){return new F(function(){return A(_Xh,[_Xt,_Xu,new T(function(){return B(_ds(_Xs,_Xv));})]);});},function(_Xw){return new F(function(){return A(_Xi,[new T(function(){return B(_ds(_Xs,_Xw));})]);});});});},_Xi);});};return new F(function(){return _ed(_iz,_W0,function(_Xx,_Xy,_Xz){return new F(function(){return _Xd(_Xy,_W1,_W2,function(_XA,_XB,_XC){return new F(function(){return A(_W1,[_XA,_XB,new T(function(){return B(_ds(_Xz,_XC));})]);});},function(_XD){return new F(function(){return A(_W2,[new T(function(){return B(_ds(_Xz,_XD));})]);});});});},_W2,function(_XE,_XF,_XG){return new F(function(){return _Xd(_XF,_W1,_W2,function(_XH,_XI,_XJ){return new F(function(){return A(_W3,[_XH,_XI,new T(function(){return B(_ds(_XG,_XJ));})]);});},function(_XK){return new F(function(){return A(_W4,[new T(function(){return B(_ds(_XG,_XK));})]);});});});});});},_XL=function(_XM,_XN,_XO,_XP,_XQ){return new F(function(){return A(_Rz,[_XM,function(_XR,_XS,_XT){return new F(function(){return _VY(_XR,_XS,_XN,_XO,function(_XU,_XV,_XW){return new F(function(){return A(_XN,[_XU,_XV,new T(function(){return B(_ds(_XT,_XW));})]);});},function(_XX){return new F(function(){return A(_XO,[new T(function(){return B(_ds(_XT,_XX));})]);});});});},_XO,function(_XY,_XZ,_Y0){return new F(function(){return _VY(_XY,_XZ,_XN,_XO,function(_Y1,_Y2,_Y3){return new F(function(){return A(_XP,[_Y1,_Y2,new T(function(){return B(_ds(_Y0,_Y3));})]);});},function(_Y4){return new F(function(){return A(_XQ,[new T(function(){return B(_ds(_Y0,_Y4));})]);});});});},_XQ]);});},_Y5=function(_Y6,_Y7,_Y8,_Y9){var _Ya=function(_Yb){var _Yc=E(_Y6),_Yd=E(_Yc[2]),_Ye=function(_Yf){var _Yg=function(_Yh){return new F(function(){return A(_Y9,[new T(function(){var _Yi=E(_Yb),_Yj=E(_Yi[1]),_Yk=E(_Yf),_Yl=E(_Yk[1]),_Ym=E(_Yh),_Yn=E(_Ym[1]),_Yo=B(_cD(_Yl[1],_Yl[2],_Yl[3],_Yk[2],_Yn[1],_Yn[2],_Yn[3],_Ym[2])),_Yp=E(_Yo[1]),_Yq=B(_cD(_Yj[1],_Yj[2],_Yj[3],_Yi[2],_Yp[1],_Yp[2],_Yp[3],_Yo[2]));return [0,E(_Yq[1]),_Yq[2]];})]);});};return new F(function(){return _VE(_Yc,_Y7,_Yg,function(_Yr,_Ys,_Yt){return new F(function(){return A(_Y8,[_Yr,_Ys,new T(function(){var _Yu=E(_Yb),_Yv=E(_Yu[1]),_Yw=E(_Yf),_Yx=E(_Yw[1]),_Yy=E(_Yt),_Yz=E(_Yy[1]),_YA=B(_cD(_Yx[1],_Yx[2],_Yx[3],_Yw[2],_Yz[1],_Yz[2],_Yz[3],_Yy[2])),_YB=E(_YA[1]),_YC=B(_cD(_Yv[1],_Yv[2],_Yv[3],_Yu[2],_YB[1],_YB[2],_YB[3],_YA[2]));return [0,E(_YC[1]),_YC[2]];})]);});},_Yg);});};return new F(function(){return _SU(_Yc[1],_Yd[1],_Yd[2],_Yd[3],_Yc[3],_Y7,_Ye,_Ye);});};return new F(function(){return _XL(_Y6,_Y7,_Ya,_Y8,_Ya);});},_YD=function(_YE,_YF,_YG,_YH,_YI){return new F(function(){return _Y5(_YE,_YF,_YH,_YI);});},_Dj=function(_YJ,_YK,_YL,_YM,_YN){return new F(function(){return _dA(_YD,_YJ,function(_YO,_YP,_YQ){return new F(function(){return _vZ(_YO,_YP,_YK,function(_YR,_YS,_YT){return new F(function(){return A(_YK,[_YR,_YS,new T(function(){return B(_ds(_YQ,_YT));})]);});});});},_YL,function(_YU,_YV,_YW){return new F(function(){return _vZ(_YU,_YV,_YK,function(_YX,_YY,_YZ){return new F(function(){return A(_YM,[_YX,_YY,new T(function(){return B(_ds(_YW,_YZ));})]);});});});},_YN);});},_Z0=function(_Z1,_Z2,_Z3){while(1){var _Z4=E(_Z2);if(!_Z4[0]){return E(_Z3)[0]==0?true:false;}else{var _Z5=E(_Z3);if(!_Z5[0]){return false;}else{if(!B(A(_84,[_Z1,_Z4[1],_Z5[1]]))){return false;}else{_Z2=_Z4[2];_Z3=_Z5[2];continue;}}}}},_Z6=function(_Z7,_Z8,_Z9){var _Za=E(_Z8),_Zb=E(_Z9);return !B(_Z0(_Z7,_Za[1],_Zb[1]))?true:!B(A(_84,[_Z7,_Za[2],_Zb[2]]))?true:false;},_Zc=function(_Zd,_Ze,_Zf,_Zg,_Zh){return !B(_Z0(_Zd,_Ze,_Zg))?false:B(A(_84,[_Zd,_Zf,_Zh]));},_Zi=function(_Zj,_Zk,_Zl){var _Zm=E(_Zk),_Zn=E(_Zl);return new F(function(){return _Zc(_Zj,_Zm[1],_Zm[2],_Zn[1],_Zn[2]);});},_Zo=function(_Zp){return [0,function(_Zq,_Zr){return new F(function(){return _Zi(_Zp,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _Z6(_Zp,_Zq,_Zr);});}];},_Zs=function(_Zt,_Zu,_Zv,_Zw,_Zx,_Zy,_Zz,_ZA,_ZB){return new F(function(){return _l0(B(_aA(_Zt,_Zu,_Zv,_Zw,_Zx,_Zy,_Zz,_ZA)),B(_aA(_Zt,_Zu,_Zv,_Zw,_Zx,_Zy,_Zz,_ZB)));});},_ZC=function(_ZD,_ZE,_ZF,_ZG,_ZH,_ZI,_ZJ,_ZK,_ZL){return !B(_Zs(_ZD,_ZE,_ZF,_ZG,_ZH,_ZI,_ZJ,_ZK,_ZL))?true:false;},_ZM=function(_ZN,_ZO,_ZP,_ZQ,_ZR,_ZS,_ZT){return [0,function(_bi,_bj){return new F(function(){return _Zs(_ZN,_ZO,_ZP,_ZQ,_ZR,_ZS,_ZT,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _ZC(_ZN,_ZO,_ZP,_ZQ,_ZR,_ZS,_ZT,_bi,_bj);});}];},_ZU=function(_ZV,_ZW,_ZX){var _ZY=E(_ZW),_ZZ=E(_ZX);return !B(_Z0(_ZV,_ZY[1],_ZZ[1]))?true:!B(A(_84,[_ZV,_ZY[2],_ZZ[2]]))?true:false;},_100=function(_101,_102,_103){var _104=E(_102),_105=E(_103);return new F(function(){return _Zc(_101,_104[1],_104[2],_105[1],_105[2]);});},_106=function(_107){return [0,function(_Zq,_Zr){return new F(function(){return _100(_107,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _ZU(_107,_Zq,_Zr);});}];},_108=function(_109,_10a,_10b){var _10c=E(_109);switch(_10c[0]){case 0:var _10d=E(_10a);return _10d[0]==0?!B(_l0(_10c[3],_10d[3]))?[0]:[1,_10b]:[0];case 1:var _10e=E(_10a);return _10e[0]==1?!B(_l0(_10c[3],_10e[3]))?[0]:[1,_10b]:[0];case 2:var _10f=E(_10a);return _10f[0]==2?!B(_l0(_10c[3],_10f[3]))?[0]:[1,_10b]:[0];case 3:var _10g=E(_10a);return _10g[0]==3?!B(_l0(_10c[3],_10g[3]))?[0]:[1,_10b]:[0];case 4:var _10h=E(_10a);return _10h[0]==4?!B(_l0(_10c[3],_10h[3]))?[0]:[1,_10b]:[0];case 5:var _10i=E(_10a);return _10i[0]==5?!B(_l0(_10c[3],_10i[3]))?[0]:[1,_10b]:[0];case 6:var _10j=E(_10a);return _10j[0]==6?!B(_l0(_10c[3],_10j[3]))?[0]:[1,_10b]:[0];case 7:var _10k=E(_10a);return _10k[0]==7?!B(_l0(_10c[3],_10k[3]))?[0]:[1,_10b]:[0];case 8:var _10l=E(_10a);return _10l[0]==8?!B(_l0(_10c[3],_10l[3]))?[0]:[1,_10b]:[0];default:var _10m=E(_10a);return _10m[0]==9?!B(_l0(_10c[3],_10m[3]))?[0]:[1,_10b]:[0];}},_10n=new T(function(){return B(_3B("Carnap/Core/Data/AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_10o=function(_10p,_10q){return [3,_,_10p,_10q];},_10r=function(_10s,_10t,_10u){while(1){var _10v=E(_10u);if(!_10v[0]){return [0];}else{var _10w=E(_10v[1]),_10x=B(A(_10s,[_10t,_10w[2],_10w[3]]));if(!_10x[0]){_10u=_10v[2];continue;}else{return E(_10x);}}}},_10y=function(_10z,_10A){while(1){var _10B=(function(_10C,_10D){var _10E=E(_10D);switch(_10E[0]){case 2:var _10F=B(_10r(_108,_10E[2],_10C));if(!_10F[0]){return E(_10E);}else{var _10G=_10C;_10A=_10F[1];_10z=_10G;return null;}break;case 4:var _10H=_10E[3],_10I=B(_10r(_108,_10E[2],_10C));if(!_10I[0]){return E(_10E);}else{var _10J=E(_10I[1]);switch(_10J[0]){case 3:return E(_10J[3])[0]==0?B(_10o(_10J[2],_10H)):E(_10E);case 4:if(!E(_10J[3])[0]){var _10G=_10C;_10A=[4,_,_10J[2],_10H];_10z=_10G;return null;}else{return E(_10E);}break;default:return E(_10E);}}break;case 6:var _10K=_10E[3],_10L=_10E[4],_10M=B(_10r(_108,_10E[2],_10C));if(!_10M[0]){return E(_10E);}else{var _10N=E(_10M[1]);switch(_10N[0]){case 5:if(!E(_10N[3])[0]){if(!E(_10N[4])[0]){var _10G=_10C;_10A=[5,_,_10N[2],_10K,_10L];_10z=_10G;return null;}else{return E(_10E);}}else{return E(_10E);}break;case 6:if(!E(_10N[3])[0]){if(!E(_10N[4])[0]){var _10G=_10C;_10A=[6,_,_10N[2],_10K,_10L];_10z=_10G;return null;}else{return E(_10E);}}else{return E(_10E);}break;default:return E(_10E);}}break;case 7:return [7,_,_10E[2],new T(function(){return B(_10y(_10C,_10E[3]));})];case 8:var _10O=_10E[2],_10P=_10E[3],_10Q=B(_10r(_108,_10O,_10C));if(!_10Q[0]){return [8,_,_10O,new T(function(){return B(_10y(_10C,_10P));})];}else{var _10R=E(_10Q[1]);switch(_10R[0]){case 7:return E(_10R[3])[0]==0?[7,_,_10R[2],new T(function(){return B(_10y(_10C,_10P));})]:[8,_,_10O,new T(function(){return B(_10y(_10C,_10P));})];case 8:if(!E(_10R[3])[0]){var _10G=_10C;_10A=[8,_,_10R[2],_10P];_10z=_10G;return null;}else{return [8,_,_10O,new T(function(){return B(_10y(_10C,_10P));})];}break;default:return [8,_,_10O,new T(function(){return B(_10y(_10C,_10P));})];}}break;case 9:return [9,_,_10E[2],new T(function(){return B(_10y(_10C,_10E[3]));}),new T(function(){return B(_10y(_10C,_10E[4]));})];case 10:var _10S=_10E[2],_10T=_10E[3],_10U=_10E[4],_10V=B(_10r(_108,_10S,_10C));if(!_10V[0]){return [10,_,_10S,new T(function(){return B(_10y(_10C,_10T));}),new T(function(){return B(_10y(_10C,_10U));})];}else{var _10W=E(_10V[1]);switch(_10W[0]){case 9:return E(_10W[3])[0]==0?E(_10W[4])[0]==0?[9,_,_10W[2],new T(function(){return B(_10y(_10C,B(_10y(_10C,_10T))));}),new T(function(){return B(_10y(_10C,B(_10y(_10C,_10U))));})]:[10,_,_10S,new T(function(){return B(_10y(_10C,_10T));}),new T(function(){return B(_10y(_10C,_10U));})]:[10,_,_10S,new T(function(){return B(_10y(_10C,_10T));}),new T(function(){return B(_10y(_10C,_10U));})];case 10:if(!E(_10W[3])[0]){if(!E(_10W[4])[0]){var _10G=_10C;_10A=[10,_,_10W[2],_10T,_10U];_10z=_10G;return null;}else{return [10,_,_10S,new T(function(){return B(_10y(_10C,_10T));}),new T(function(){return B(_10y(_10C,_10U));})];}}else{return [10,_,_10S,new T(function(){return B(_10y(_10C,_10T));}),new T(function(){return B(_10y(_10C,_10U));})];}break;default:return [10,_,_10S,new T(function(){return B(_10y(_10C,_10T));}),new T(function(){return B(_10y(_10C,_10U));})];}}break;case 11:return [11,_,_10E[2],function(_10X){return new F(function(){return _10y(_10C,B(A(_10E[3],[_10X])));});}];case 12:var _10Y=_10E[2],_10Z=_10E[3],_110=B(_10r(_108,_10Y,_10C));if(!_110[0]){return [12,_,_10Y,function(_111){return new F(function(){return _10y(_10C,B(A(_10Z,[_111])));});}];}else{var _112=E(_110[1]);switch(_112[0]){case 11:return [11,_,_112[2],function(_113){return new F(function(){return _10y(_10C,B(A(_10Z,[_113])));});}];case 12:var _10G=_10C;_10A=[12,_,_112[2],_10Z];_10z=_10G;return null;default:return [12,_,_10Y,function(_114){return new F(function(){return _10y(_10C,B(A(_10Z,[_114])));});}];}}break;default:return E(_10E);}})(_10z,_10A);if(_10B!=null){return _10B;}}},_115=function(_116,_117){var _118=E(_117);if(!_118[0]){var _119=B(_10r(_108,_118[1],_116));if(!_119[0]){return E(_118);}else{var _11a=E(_119[1]);return _11a[0]==0?E(_10n):[1,new T(function(){return B(_7X(function(_11b){return new F(function(){return _10y(_116,_11b);});},_11a[1]));})];}}else{return [1,new T(function(){return B(_7X(function(_11c){return new F(function(){return _10y(_116,_11c);});},_118[1]));})];}},_11d=function(_11e,_11f,_11g,_11h,_11i,_11j,_11k,_11l,_11m){var _11n=E(_11m);return [0,new T(function(){return B(_7X(function(_11o){return new F(function(){return _115(_11l,_11o);});},_11n[1]));}),new T(function(){return B(_115(_11l,_11n[2]));})];},_11p=function(_11q,_11r,_11s,_11t,_11u,_11v,_11w,_11x,_11y){var _11z=E(_11y);return [0,new T(function(){return B(_7X(function(_11A){return new F(function(){return _11d(_11q,_11r,_11s,_11t,_11u,_11v,_11w,_11x,_11A);});},_11z[1]));}),new T(function(){return B(_11d(_11q,_11r,_11s,_11t,_11u,_11v,_11w,_11x,_11z[2]));})];},_11B=function(_11C){return E(E(_11C)[1]);},_11D=function(_11E,_11F){var _11G=E(_11F);return new F(function(){return A(_11B,[_11G[1],E(_11E)[2],_11G[2]]);});},_11H=function(_11I,_11J,_11K){var _11L=E(_11K);if(!_11L[0]){return [0];}else{var _11M=_11L[1],_11N=_11L[2];return !B(A(_11I,[_11J,_11M]))?[1,_11M,new T(function(){return B(_11H(_11I,_11J,_11N));})]:E(_11N);}},_11O=function(_11P,_11Q,_11R){while(1){var _11S=E(_11R);if(!_11S[0]){return false;}else{if(!B(A(_11P,[_11Q,_11S[1]]))){_11R=_11S[2];continue;}else{return true;}}}},_11T=function(_11U,_11V){var _11W=function(_11X,_11Y){while(1){var _11Z=(function(_120,_121){var _122=E(_120);if(!_122[0]){return [0];}else{var _123=_122[1],_124=_122[2];if(!B(_11O(_11U,_123,_121))){return [1,_123,new T(function(){return B(_11W(_124,[1,_123,_121]));})];}else{_11X=_124;var _125=_121;_11Y=_125;return null;}}})(_11X,_11Y);if(_11Z!=null){return _11Z;}}};return new F(function(){return _11W(_11V,_9);});},_126=function(_127,_128,_129){return new F(function(){return _e(_128,new T(function(){return B((function(_12a,_12b){while(1){var _12c=E(_12b);if(!_12c[0]){return E(_12a);}else{var _12d=B(_11H(_127,_12c[1],_12a));_12b=_12c[2];_12a=_12d;continue;}}})(B(_11T(_127,_129)),_128));},1));});},_12e=function(_12f,_12g){while(1){var _12h=(function(_12i,_12j){var _12k=E(_12j);switch(_12k[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_12i,_12k[2]],_9];case 3:var _12l=_12i;_12g=_12k[3];_12f=_12l;return null;case 4:return new F(function(){return _126(_11D,[1,[0,_12i,_12k[2]],_9],new T(function(){return B(_12e(_12i,_12k[3]));},1));});break;case 5:return new F(function(){return _126(_11D,B(_12e(_12i,_12k[3])),new T(function(){return B(_12e(_12i,_12k[4]));},1));});break;default:return new F(function(){return _126(_11D,B(_126(_11D,[1,[0,_12i,_12k[2]],_9],new T(function(){return B(_12e(_12i,_12k[3]));},1))),new T(function(){return B(_12e(_12i,_12k[4]));},1));});}})(_12f,_12g);if(_12h!=null){return _12h;}}},_12m=function(_12n,_12o,_12p,_12q){while(1){var _12r=(function(_12s,_12t,_12u,_12v){var _12w=E(_12v);switch(_12w[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_12s,_12w[2]],_9];case 3:return new F(function(){return _12e(_12s,_12w[3]);});break;case 4:return new F(function(){return _126(_11D,[1,[0,_12s,_12w[2]],_9],new T(function(){return B(_12e(_12s,_12w[3]));},1));});break;case 5:return new F(function(){return _126(_11D,B(_12e(_12s,_12w[3])),new T(function(){return B(_12e(_12s,_12w[4]));},1));});break;case 6:return new F(function(){return _126(_11D,B(_126(_11D,[1,[0,_12s,_12w[2]],_9],new T(function(){return B(_12e(_12s,_12w[3]));},1))),new T(function(){return B(_12e(_12s,_12w[4]));},1));});break;case 7:var _12x=_12s,_12y=_12t,_12z=_12u;_12q=_12w[3];_12n=_12x;_12o=_12y;_12p=_12z;return null;case 8:return new F(function(){return _126(_11D,[1,[0,_12s,_12w[2]],_9],new T(function(){return B(_12m(_12s,_12t,_12u,_12w[3]));},1));});break;case 9:return new F(function(){return _126(_11D,B(_12m(_12s,_12t,_12u,_12w[3])),new T(function(){return B(_12m(_12s,_12t,_12u,_12w[4]));},1));});break;case 10:return new F(function(){return _126(_11D,B(_126(_11D,[1,[0,_12s,_12w[2]],_9],new T(function(){return B(_12m(_12s,_12t,_12u,_12w[3]));},1))),new T(function(){return B(_12m(_12s,_12t,_12u,_12w[4]));},1));});break;case 11:var _12x=_12s,_12y=_12t,_12z=_12u;_12q=B(A(_12w[3],[_ae]));_12n=_12x;_12o=_12y;_12p=_12z;return null;default:return new F(function(){return _126(_11D,[1,[0,_12s,_12w[2]],_9],new T(function(){return B(_12m(_12s,_12t,_12u,B(A(_12w[3],[_ae]))));},1));});}})(_12n,_12o,_12p,_12q);if(_12r!=null){return _12r;}}},_12A=function(_12B,_12C,_12D,_12E,_12F){var _12G=function(_12H){return new F(function(){return _12m(_12B,_12C,_12D,_12H);});};return new F(function(){return _e(B(_7r(B(_7X(function(_12I){var _12J=E(_12I);if(!_12J[0]){return [1,[0,_12B,_12J[1]],_9];}else{return new F(function(){return _7r(B(_7X(_12G,_12J[1])));});}},_12E)))),new T(function(){var _12K=E(_12F);if(!_12K[0]){var _12L=[1,[0,_12B,_12K[1]],_9];}else{var _12L=B(_7r(B(_7X(_12G,_12K[1]))));}return _12L;},1));});},_12M=function(_12N,_12O,_12P,_12Q,_12R,_12S,_12T,_12U,_12V){var _12W=E(_12V);return new F(function(){return _e(B(_7r(B(_7X(function(_12X){var _12Y=E(_12X);return new F(function(){return _12A(_12N,_12R,_12S,_12Y[1],_12Y[2]);});},_12W[1])))),new T(function(){var _12Z=E(_12W[2]);return B(_12A(_12N,_12R,_12S,_12Z[1],_12Z[2]));},1));});},_130=function(_131,_132,_133,_134,_135,_136,_137,_138,_139,_13a,_13b){return [0,_131,_132,_133,_134,function(_11A){return new F(function(){return _12M(_131,_135,_136,_137,_138,_139,_13a,_13b,_11A);});},function(_13c,_11A){return new F(function(){return _11p(_135,_136,_137,_138,_139,_13a,_13b,_13c,_11A);});}];},_13d=function(_13e){return E(E(_13e)[2]);},_13f=function(_13g){return E(E(_13g)[1]);},_13h=[0,_13f,_13d],_13i=[0,125],_13j=new T(function(){return B(unCStr("given = "));}),_13k=new T(function(){return B(unCStr(", "));}),_13l=new T(function(){return B(unCStr("needed = "));}),_13m=new T(function(){return B(unCStr("AbsRule {"));}),_13n=[0,0],_13o=function(_13p){return E(E(_13p)[3]);},_13q=function(_13r){return E(E(_13r)[1]);},_13s=function(_13t,_13u,_13v,_13w){var _13x=function(_13y){return new F(function(){return _e(_13m,new T(function(){return B(_e(_13l,new T(function(){return B(A(new T(function(){return B(A(_13o,[_13t,_13v]));}),[new T(function(){return B(_e(_13k,new T(function(){return B(_e(_13j,new T(function(){return B(A(new T(function(){return B(A(_13q,[_13t,_13n,_13w]));}),[[1,_13i,_13y]]));},1)));},1)));})]));},1)));},1));});};return _13u<11?E(_13x):function(_13z){return [1,_E,new T(function(){return B(_13x([1,_D,_13z]));})];};},_13A=function(_13B,_13C){var _13D=E(_13C);return new F(function(){return A(_13s,[_13B,0,_13D[1],_13D[2],_9]);});},_13E=function(_13F,_13G,_13H){return new F(function(){return _2T(function(_13I){var _13J=E(_13I);return new F(function(){return _13s(_13F,0,_13J[1],_13J[2]);});},_13G,_13H);});},_13K=function(_13L,_13M,_13N){var _13O=E(_13N);return new F(function(){return _13s(_13L,E(_13M)[1],_13O[1],_13O[2]);});},_13P=function(_13Q){return [0,function(_Zq,_Zr){return new F(function(){return _13K(_13Q,_Zq,_Zr);});},function(_Zr){return new F(function(){return _13A(_13Q,_Zr);});},function(_Zq,_Zr){return new F(function(){return _13E(_13Q,_Zq,_Zr);});}];},_13R=new T(function(){return B(unCStr("Sequent "));}),_13S=[0,11],_13T=[0,32],_13U=function(_13V,_13W,_13X,_13Y){var _13Z=new T(function(){return B(A(_13q,[_13V,_13S,_13Y]));}),_140=new T(function(){return B(A(_13o,[_13V,_13X]));});return _13W<11?function(_141){return new F(function(){return _e(_13R,new T(function(){return B(A(_140,[[1,_13T,new T(function(){return B(A(_13Z,[_141]));})]]));},1));});}:function(_142){return [1,_E,new T(function(){return B(_e(_13R,new T(function(){return B(A(_140,[[1,_13T,new T(function(){return B(A(_13Z,[[1,_D,_142]]));})]]));},1)));})];};},_143=function(_144,_145){var _146=E(_145);return new F(function(){return A(_13U,[_144,0,_146[1],_146[2],_9]);});},_147=function(_148,_149,_14a){return new F(function(){return _2T(function(_14b){var _14c=E(_14b);return new F(function(){return _13U(_148,0,_14c[1],_14c[2]);});},_149,_14a);});},_14d=function(_14e,_14f,_14g){var _14h=E(_14g);return new F(function(){return _13U(_14e,E(_14f)[1],_14h[1],_14h[2]);});},_14i=function(_14j){return [0,function(_Zq,_Zr){return new F(function(){return _14d(_14j,_Zq,_Zr);});},function(_Zr){return new F(function(){return _143(_14j,_Zr);});},function(_Zq,_Zr){return new F(function(){return _147(_14j,_Zq,_Zr);});}];},_14k=function(_14l,_14m){return new F(function(){return _e(B(_a1(_14l)),_14m);});},_14n=function(_14o,_14p){return new F(function(){return _2T(_14k,_14o,_14p);});},_14q=function(_14r,_14s,_14t){return new F(function(){return _e(B(_a1(_14s)),_14t);});},_14u=[0,_14q,_a1,_14n],_14v=function(_14w,_14x,_14y,_14z,_14A,_14B,_14C,_14D,_14E,_14F,_14G,_14H){var _14I=E(_14H);return new F(function(){return _12A(_14w,_14D,_14E,_14I[1],_14I[2]);});},_14J=function(_14K,_14L,_14M,_14N,_14O,_14P,_14Q,_14R,_14S,_14T,_14U){return [0,_14K,_14L,_14M,_14N,function(_11A){return new F(function(){return _14v(_14K,_14L,_14M,_14N,_14O,_14P,_14Q,_14R,_14S,_14T,_14U,_11A);});},function(_13c,_11A){return new F(function(){return _11d(_14O,_14P,_14Q,_14R,_14S,_14T,_14U,_13c,_11A);});}];},_14V=function(_14W,_14X){return [0];},_14Y=function(_14Z,_150,_151,_152,_153,_154,_155,_156,_157,_158,_159,_15a,_15b,_15c){return [0,_14Z,_150,_14V,_1];},_15d=function(_15e,_15f,_15g,_15h,_15i,_15j,_15k,_15l,_15m,_15n,_15o,_15p){var _15q=E(_15p);if(!_15q[0]){return [1,[0,_15e,_15q[1]],_9];}else{return new F(function(){return _7r(B(_7X(function(_15r){return new F(function(){return _12m(_15e,_15l,_15m,_15r);});},_15q[1])));});}},_15s=function(_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D){return [0,_15t,_15u,_15v,_15w,function(_11A){return new F(function(){return _15d(_15t,_15u,_15v,_15w,_15x,_15y,_15z,_15A,_15B,_15C,_15D,_11A);});},_115];},_15E=new T(function(){return B(_BP("w_sAyu{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r14r}\n                  sv{tv aAcx} [tv] quant{tv aAcv} [tv]"));}),_15F=new T(function(){return B(_BP("w_sAyt{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv aAcv} [tv]"));}),_15G=new T(function(){return B(_BP("w_sAys{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv aAcu} [tv]"));}),_15H=new T(function(){return B(_BP("w_sAyr{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv aAcx} [tv]"));}),_15I=new T(function(){return B(_BP("w_sAyq{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv aAct} [tv]"));}),_15J=new T(function(){return B(_BP("w_sAyp{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv aAcw} [tv]"));}),_15K=new T(function(){return B(_BP("w_sAyv{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13B}\n                  sv{tv aAcx} [tv]"));}),_15L=new T(function(){return B(_BP("w_sAyo{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aAcv} [tv]"));}),_15M=new T(function(){return B(_BP("w_sAyn{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv aAcu} [tv]"));}),_15N=new T(function(){return B(_BP("w_sAym{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv aAcx} [tv]"));}),_15O=new T(function(){return B(_BP("w_sAyl{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv aAct} [tv]"));}),_15P=new T(function(){return B(_BP("w_sAyk{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv aAcw} [tv]"));}),_15Q=function(_15R,_15S){return function(_15T,_15U){var _15V=E(_15T);return _15V[0]==0?[1,[0,new T(function(){return B(_15W(_15R,_15S,_15P,_15O,_15N,_15M,_15L,_15J,_15I,_15H,_15G,_15F,_15E,_15K));}),_15V[1],_15U]]:[0];};},_15X=function(_15Y){return [0,E(_15Y)];},_15W=function(_15Z,_160,_161,_162,_163,_164,_165,_166,_167,_168,_169,_16a,_16b,_16c){return [0,_15Z,_160,new T(function(){return B(_15Q(_15Z,_160));}),_15X];},_16d=[1,_9],_16e=function(_16f,_16g){while(1){var _16h=E(_16f);if(!_16h[0]){return E(_16g);}else{_16f=_16h[2];var _16i=_16g+1|0;_16g=_16i;continue;}}},_16j=[0,95],_16k=[1,_16j,_9],_16l=[1,_16k,_9],_16m=function(_16n,_16o,_16p){return !B(_l0(B(A(_16n,[_16o,_16l])),B(A(_16n,[_16p,_16l]))))?true:false;},_16q=function(_16r){return [0,function(_16s,_16t){return new F(function(){return _l0(B(A(_16r,[_16s,_16l])),B(A(_16r,[_16t,_16l])));});},function(_bi,_bj){return new F(function(){return _16m(_16r,_bi,_bj);});}];},_16u=function(_16v,_16w){return new F(function(){return _10y(_16v,_16w);});},_16x=function(_16y,_16z,_16A,_16B,_16C,_16D,_16E,_16F,_16G,_16H,_16I){return [0,_16y,_16z,_16A,_16B,function(_16J){return new F(function(){return _12m(_16y,_16F,_16G,_16J);});},_16u];},_16K=new T(function(){return B(_BP("w_spqi{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.S_NextVar{tc r14r}\n                  sv{tv amni} [tv] quant{tv amng} [tv]"));}),_16L=new T(function(){return B(_BP("w_spqh{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv amng} [tv]"));}),_16M=new T(function(){return B(_BP("w_spqg{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv amnf} [tv]"));}),_16N=new T(function(){return B(_BP("w_spqf{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv amni} [tv]"));}),_16O=new T(function(){return B(_BP("w_spqe{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv amne} [tv]"));}),_16P=new T(function(){return B(_BP("w_spqd{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv amnh} [tv]"));}),_16Q=new T(function(){return B(_BP("w_spqj{v} [lid] main:Carnap.Core.Data.AbstractSyntaxMultiUnification.SchemeVar{tc r13B}\n                  sv{tv amni} [tv]"));}),_16R=new T(function(){return B(_BP("w_spqc{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv amng} [tv]"));}),_16S=new T(function(){return B(_BP("w_spqb{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv amnf} [tv]"));}),_16T=new T(function(){return B(_BP("w_spqa{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv amni} [tv]"));}),_16U=new T(function(){return B(_BP("w_spq9{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv amne} [tv]"));}),_16V=new T(function(){return B(_BP("w_spq8{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv amnh} [tv]"));}),_16W=function(_16X,_16Y,_16Z,_170){var _171=E(_16Z);switch(_171[0]){case 2:return [1,[0,new T(function(){return B(_172(_16X,_16Y,_16V,_16U,_16T,_16S,_16R,_16P,_16O,_16N,_16M,_16L,_16K,_16Q));}),_171[2],_170]];case 4:var _173=_171[2];if(!E(_171[3])[0]){var _174=E(_170);switch(_174[0]){case 3:return E(_174[3])[0]==0?[1,[0,new T(function(){return B(_172(_16X,_16Y,_16V,_16U,_16T,_16S,_16R,_16P,_16O,_16N,_16M,_16L,_16K,_16Q));}),_173,_174]]:[0];case 4:return E(_174[3])[0]==0?[1,[0,new T(function(){return B(_172(_16X,_16Y,_16V,_16U,_16T,_16S,_16R,_16P,_16O,_16N,_16M,_16L,_16K,_16Q));}),_173,_174]]:[0];default:return [0];}}else{return [0];}break;case 6:var _175=_171[2];if(!E(_171[3])[0]){if(!E(_171[4])[0]){var _176=E(_170);switch(_176[0]){case 5:return E(_176[3])[0]==0?E(_176[4])[0]==0?[1,[0,new T(function(){return B(_172(_16X,_16Y,_16V,_16U,_16T,_16S,_16R,_16P,_16O,_16N,_16M,_16L,_16K,_16Q));}),_175,_176]]:[0]:[0];case 6:return E(_176[3])[0]==0?E(_176[4])[0]==0?[1,[0,new T(function(){return B(_172(_16X,_16Y,_16V,_16U,_16T,_16S,_16R,_16P,_16O,_16N,_16M,_16L,_16K,_16Q));}),_175,_176]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _177=_171[2];if(!E(_171[3])[0]){var _178=E(_170);switch(_178[0]){case 7:return E(_178[3])[0]==0?[1,[0,new T(function(){return B(_172(_16X,_16Y,_16V,_16U,_16T,_16S,_16R,_16P,_16O,_16N,_16M,_16L,_16K,_16Q));}),_177,_178]]:[0];case 8:return E(_178[3])[0]==0?[1,[0,new T(function(){return B(_172(_16X,_16Y,_16V,_16U,_16T,_16S,_16R,_16P,_16O,_16N,_16M,_16L,_16K,_16Q));}),_177,_178]]:[0];default:return [0];}}else{return [0];}break;case 10:var _179=_171[2];if(!E(_171[3])[0]){if(!E(_171[4])[0]){var _17a=E(_170);switch(_17a[0]){case 9:return E(_17a[3])[0]==0?E(_17a[4])[0]==0?[1,[0,new T(function(){return B(_172(_16X,_16Y,_16V,_16U,_16T,_16S,_16R,_16P,_16O,_16N,_16M,_16L,_16K,_16Q));}),_179,_17a]]:[0]:[0];case 10:return E(_17a[3])[0]==0?E(_17a[4])[0]==0?[1,[0,new T(function(){return B(_172(_16X,_16Y,_16V,_16U,_16T,_16S,_16R,_16P,_16O,_16N,_16M,_16L,_16K,_16Q));}),_179,_17a]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_17b=new T(function(){return B(_3B("Carnap/Core/Data/AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_17c=function(_17d){var _17e=E(_17d);switch(_17e[0]){case 3:return [2,_,_17e];case 4:return [4,_,_17e,_V];case 5:return [6,_,_17e,_V,_V];case 6:return [8,_,_17e,_S];case 7:return [10,_,_17e,_S,_S];default:return E(_17b);}},_172=function(_17f,_17g,_17h,_17i,_17j,_17k,_17l,_17m,_17n,_17o,_17p,_17q,_17r,_17s){return [0,_17f,_17g,function(_17t,_17u){return new F(function(){return _16W(_17f,_17g,_17t,_17u);});},_17c];},_17v=function(_17w,_17x,_17y){return new F(function(){return _2T(function(_17z,_17A){return new F(function(){return _e(B(A(_17w,[_17z,_16l])),_17A);});},_17x,_17y);});},_17B=function(_17C){return [0,function(_17D,_17E,_17F){return new F(function(){return _e(B(A(_17C,[_17E,_16l])),_17F);});},function(_17G){return new F(function(){return A(_17C,[_17G,_16l]);});},function(_bi,_bj){return new F(function(){return _17v(_17C,_bi,_bj);});}];},_17H=[1,_9],_17I=function(_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_17T,_17U){var _17V=E(_17T);if(_17V[0]==2){return E(_17H);}else{var _17W=E(_17U);if(_17W[0]==2){return E(_17H);}else{var _17X=function(_17Y){var _17Z=function(_180){var _181=function(_182){var _183=function(_184){var _185=function(_186){var _187=function(_188){var _189=function(_18a){var _18b=function(_18c){var _18d=function(_18e){var _18f=function(_18g){var _18h=function(_18i){var _18j=function(_18k){var _18l=E(_17V);switch(_18l[0]){case 1:var _18m=E(_17W);return _18m[0]==1?!B(A(_17K,[_18l[2],_18m[2]]))?[0]:E(_17H):[0];case 3:var _18n=E(_17W);return _18n[0]==3?!B(A(_17J,[_18l[2],_18n[2]]))?[0]:E(_17H):[0];case 4:var _18o=_18l[2],_18p=E(_17W);switch(_18p[0]){case 3:return [1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,[4,_,_18o,_V],[3,_,_18p[2],_V]]));}),_9]];case 4:return [1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,[4,_,_18o,_V],[4,_,_18p[2],_V]]));}),_9]];default:return [0];}break;case 5:var _18r=E(_17W);return _18r[0]==5?!B(A(_17J,[_18l[2],_18r[2]]))?[0]:E(_17H):[0];case 6:var _18s=_18l[2],_18t=E(_17W);switch(_18t[0]){case 5:return [1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,[6,_,_18s,_V,_V],[5,_,_18t[2],_V,_V]]));}),_9]];case 6:return [1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,[6,_,_18s,_V,_V],[6,_,_18t[2],_V,_V]]));}),_9]];default:return [0];}break;case 7:var _18u=E(_17W);return _18u[0]==7?!B(A(_17L,[_18l[2],_18u[2]]))?[0]:[1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_18l[3],_18u[3]]));}),_9]]:[0];case 8:var _18v=_18l[2],_18w=_18l[3],_18x=E(_17W);switch(_18x[0]){case 7:return [1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,[8,_,_18v,_S],[7,_,_18x[2],_S]]));}),[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_18w,_18x[3]]));}),_9]]];case 8:return [1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,[8,_,_18v,_S],[8,_,_18x[2],_S]]));}),[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_18w,_18x[3]]));}),_9]]];default:return [0];}break;case 9:var _18y=E(_17W);return _18y[0]==9?!B(A(_17L,[_18l[2],_18y[2]]))?[0]:[1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_18l[3],_18y[3]]));}),[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_18l[4],_18y[4]]));}),_9]]]:[0];case 10:var _18z=_18l[2],_18A=_18l[3],_18B=_18l[4],_18C=function(_18D){var _18E=E(_17W);switch(_18E[0]){case 9:return [1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,[10,_,_18z,_S,_S],[9,_,_18E[2],_S,_S]]));}),[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_18A,_18E[3]]));}),[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_18B,_18E[4]]));}),_9]]]];case 10:return [1,[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,[10,_,_18z,_S,_S],[10,_,_18E[2],_S,_S]]));}),[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_18A,_18E[3]]));}),[1,new T(function(){return B(A(_18q,[_17J,_17K,_17L,_17M,_17N,_17O,_17P,_17Q,_17R,_17S,_18B,_18E[4]]));}),_9]]]];default:return [0];}};return E(_18A)[0]==0?E(_18B)[0]==0?E(_17H):B(_18C(_)):B(_18C(_));default:return [0];}},_18F=E(_17W);return _18F[0]==10?E(_18F[3])[0]==0?E(_18F[4])[0]==0?E(_17H):B(_18j(_)):B(_18j(_)):B(_18j(_));},_18G=E(_17V);return _18G[0]==8?E(_18G[3])[0]==0?E(_17H):B(_18h(_)):B(_18h(_));},_18H=E(_17W);switch(_18H[0]){case 6:return E(_18H[3])[0]==0?E(_18H[4])[0]==0?E(_17H):B(_18f(_)):B(_18f(_));case 8:return E(_18H[3])[0]==0?E(_17H):B(_18f(_));default:return new F(function(){return _18f(_);});}},_18I=E(_17V);return _18I[0]==6?E(_18I[3])[0]==0?E(_18I[4])[0]==0?E(_17H):B(_18d(_)):B(_18d(_)):B(_18d(_));},_18J=E(_17W);return _18J[0]==4?E(_18J[3])[0]==0?E(_17H):B(_18b(_)):B(_18b(_));},_18K=E(_17V);switch(_18K[0]){case 4:return E(_18K[3])[0]==0?E(_17H):B(_189(_));case 9:return E(_18K[3])[0]==0?E(_18K[4])[0]==0?E(_17H):B(_189(_)):B(_189(_));default:return new F(function(){return _189(_);});}},_18L=E(_17W);return _18L[0]==9?E(_18L[3])[0]==0?E(_18L[4])[0]==0?E(_17H):B(_187(_)):B(_187(_)):B(_187(_));},_18M=E(_17V);return _18M[0]==7?E(_18M[3])[0]==0?E(_17H):B(_185(_)):B(_185(_));},_18N=E(_17W);switch(_18N[0]){case 5:return E(_18N[3])[0]==0?E(_18N[4])[0]==0?E(_17H):B(_183(_)):B(_183(_));case 7:return E(_18N[3])[0]==0?E(_17H):B(_183(_));default:return new F(function(){return _183(_);});}},_18O=E(_17V);return _18O[0]==5?E(_18O[3])[0]==0?E(_18O[4])[0]==0?E(_17H):B(_181(_)):B(_181(_)):B(_181(_));},_18P=E(_17W);return _18P[0]==3?E(_18P[3])[0]==0?E(_17H):B(_17Z(_)):B(_17Z(_));},_18Q=E(_17V);return _18Q[0]==3?E(_18Q[3])[0]==0?E(_17H):B(_17X(_)):B(_17X(_));}}},_18R=function(_18S,_18T,_18U){return [0,_18S,_18T,_18U];},_18V=new T(function(){return B(_BP("w_spqr{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ammD} [tv]"));}),_18W=new T(function(){return B(_BP("w_spqn{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ammE} [tv]"));}),_18X=function(_18Y){return [0,function(_18Z,_190){return B(A(_18Y,[_18Z,_190,_1]))[0]==0?false:true;},function(_191,_192){return B(A(_18Y,[_191,_192,_1]))[0]==0?true:false;}];},_193=new T(function(){return B(_18X(_108));}),_18q=function(_194,_195,_196,_197,_198,_199,_19a,_19b,_19c,_19d){var _19e=function(_19f,_19g){return new F(function(){return _af(_198,_19a,_19b,_199,_197,_19c,_19d,_19f);});};return function(_lH,_19h){return new F(function(){return _18R(new T(function(){return B(_172(function(_19i,_19j){return new F(function(){return _17I(_194,_195,_196,_197,_198,_199,_19a,_19b,_19c,_19d,_19i,_19j);});},new T(function(){return B(_16x(_193,_14u,new T(function(){return B(_16q(_19e));}),new T(function(){return B(_17B(_19e));}),_198,_19a,_19b,_197,_199,_19c,_19d));}),_18W,_194,_195,_196,_18V,_197,_198,_199,_19a,_19b,_19c,_19d));}),_lH,_19h);});};},_19k=function(_19l,_19m,_19n){var _19o=E(_19m);if(!_19o[0]){return [0];}else{var _19p=E(_19n);return _19p[0]==0?[0]:[1,new T(function(){return B(A(_19l,[_19o[1],_19p[1]]));}),new T(function(){return B(_19k(_19l,_19o[2],_19p[2]));})];}},_19q=function(_19r,_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z,_19A,_19B,_19C){var _19D=E(_19B);if(!_19D[0]){return E(_16d);}else{var _19E=_19D[1],_19F=E(_19C);if(!_19F[0]){return E(_16d);}else{var _19G=_19F[1];return B(_16e(_19E,0))!=B(_16e(_19G,0))?[0]:[1,new T(function(){return B(_19k(new T(function(){return B(_18q(_19r,_19s,_19t,_19u,_19v,_19w,_19x,_19y,_19z,_19A));}),_19E,_19G));})];}}},_19H=new T(function(){return B(_BP("w_sAzf{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv aAcd} [tv]"));}),_19I=new T(function(){return B(_BP("w_sAzj{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aAcc} [tv]"));}),_19J=new T(function(){return B(_18X(_108));}),_19K=function(_19L,_19M,_19N,_19O,_19P,_19Q,_19R,_19S,_19T,_19U){var _19V=new T(function(){return B(_15W(function(_19W,_19X){return new F(function(){return _19q(_19L,_19M,_19N,_19O,_19P,_19Q,_19R,_19S,_19T,_19U,_19W,_19X);});},new T(function(){return B(_15s(_19J,_14u,new T(function(){return B(_ZM(_19P,_19R,_19S,_19O,_19Q,_19T,_19U));}),new T(function(){return B(_b9(_19P,_19R,_19S,_19O,_19Q,_19T,_19U));}),_19P,_19R,_19S,_19O,_19Q,_19T,_19U));}),_19H,_19L,_19M,_19N,_19I,_19O,_19P,_19Q,_19R,_19S,_19T,_19U));});return function(_19Y,_19Z){var _1a0=E(_19Y),_1a1=_1a0[1],_1a2=E(_19Z),_1a3=_1a2[1];return B(_16e(_1a1,0))!=B(_16e(_1a3,0))?[0]:[1,[1,[0,_19V,_1a0[2],_1a2[2]],new T(function(){return B(_19k(function(_13c,_11A){return [0,_19V,_13c,_11A];},_1a1,_1a3));})]];};},_1a4=new T(function(){return B(_BP("w_sABR{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv aAbK} [tv]"));}),_1a5=new T(function(){return B(_BP("w_sABV{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv aAbJ} [tv]"));}),_1a6=function(_1a7,_1a8,_1a9,_1aa,_1ab,_1ac,_1ad,_1ae,_1af,_1ag){var _1ah=new T(function(){return B(_14Y(new T(function(){return B(_19K(_1a7,_1a8,_1a9,_1aa,_1ab,_1ac,_1ad,_1ae,_1af,_1ag));}),new T(function(){return B(_14J(_19J,_14u,new T(function(){return B(_106(new T(function(){return B(_ZM(_1ab,_1ad,_1ae,_1aa,_1ac,_1af,_1ag));})));}),new T(function(){return B(_14i(new T(function(){return B(_b9(_1ab,_1ad,_1ae,_1aa,_1ac,_1af,_1ag));})));}),_1ab,_1ad,_1ae,_1aa,_1ac,_1af,_1ag));}),_1a4,_1a7,_1a8,_1a9,_1a5,_1aa,_1ab,_1ac,_1ad,_1ae,_1af,_1ag));});return function(_1ai,_1aj){var _1ak=E(_1ai),_1al=_1ak[1],_1am=E(_1aj),_1an=_1am[1];return B(_16e(_1al,0))!=B(_16e(_1an,0))?[0]:[1,[1,[0,_1ah,_1ak[2],_1am[2]],new T(function(){return B(_19k(function(_13c,_11A){return [0,_1ah,_13c,_11A];},_1al,_1an));})]];};},_1ao=function(_1ap,_1aq){while(1){var _1ar=E(_1aq);if(!_1ar[0]){return false;}else{var _1as=E(_1ar[1]);if(!B(A(_11B,[_1as[1],_1ap,_1as[2]]))){_1aq=_1ar[2];continue;}else{return true;}}}},_1at=[0,_9],_1au=function(_1av,_1aw,_1ax,_1ay,_1az,_1aA,_1aB,_1aC,_1aD,_1aE,_1aF){var _1aG=E(_1ay);return !B(A(_1aG[1],[new T(function(){return B(A(_1aD,[_1aE]));}),_1aF]))?!B(_1ao(_1aE,B(A(_1aA,[_1aF]))))?[0,[1,[0,[0,_1av,[0,_1aw,_1ax,_1aG,_1az,_1aA,_1aB],_1aC,_1aD],_1aE,_1aF],_9]]:[1,[1,_,[0,_1av,[0,_1aw,_1ax,_1aG,_1az,_1aA,_1aB],_1aC,_1aD],[3,_1ax,_1az,_1aE,_1aF]]]:E(_1at);},_1aH=function(_1aI){return new F(function(){return _3B("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:(54,15)-(56,42)|case");});},_1aJ=new T(function(){return B(_1aH(_));}),_1aK=new T(function(){return B(unCStr(": empty list"));}),_1aL=new T(function(){return B(unCStr("Prelude."));}),_1aM=function(_1aN){return new F(function(){return err(B(_e(_1aL,new T(function(){return B(_e(_1aN,_1aK));},1))));});},_1aO=new T(function(){return B(unCStr("head"));}),_1aP=new T(function(){return B(_1aM(_1aO));}),_1aQ=function(_1aR){return E(E(_1aR)[2]);},_1aS=function(_1aT,_1aU){while(1){var _1aV=E(_1aT);if(!_1aV){return E(_1aU);}else{var _1aW=E(_1aU);if(!_1aW[0]){return [0];}else{_1aT=_1aV-1|0;_1aU=_1aW[2];continue;}}}},_1aX=function(_1aY,_1aZ){var _1b0=E(_1aY)[1];return _1b0>=0?B(_1aS(_1b0,_1aZ)):E(_1aZ);},_1b1=function(_1b2){return new F(function(){return _3B("Carnap/Systems/NaturalDeduction/JudgementHandler.hs:96:31-64|function conc");});},_1b3=new T(function(){return B(_1b1(_));}),_1b4=function(_1b5){var _1b6=E(_1b5);switch(_1b6[0]){case 3:return [2,_,_1b6];case 4:return [4,_,_1b6,_V];case 5:return [6,_,_1b6,_V,_V];case 6:return [8,_,_1b6,_S];case 7:return [10,_,_1b6,_S,_S];default:return E(_17b);}},_1b7=function(_1b8){var _1b9=E(_1b8);if(!_1b9[0]){return [0];}else{var _1ba=E(_1b9[1]);if(!_1ba[0]){return [0];}else{return new F(function(){return _e(_1ba[1],new T(function(){return B(_1b7(_1b9[2]));},1));});}}},_1bb=function(_1bc){var _1bd=E(_1bc);return [0,[1,[1,new T(function(){return B(_1b7(_1bd[1]));})],_9],_1bd[2]];},_1be=function(_1bf,_1bg,_1bh){return !B(_86(_1bf,_1bg,_1bh))?E(_1bh):[1,_1bg,new T(function(){return B(_7u(function(_1bi){return !B(A(_84,[_1bf,_1bi,_1bg]))?true:false;},_1bh));})];},_1bj=function(_1bk,_1bl,_1bm,_1bn,_1bo,_1bp,_1bq){return function(_1br,_1bs){var _1bt=E(_1br);if(!_1bt[0]){return new F(function(){return _1bb(_1bs);});}else{var _1bu=E(_1bs);return [0,[1,[1,new T(function(){return B(_1be(new T(function(){return B(_16q(function(_1bv,_1bw){return new F(function(){return _af(_1bq,_1bp,_1bo,_1bm,_1bn,_1bk,_1bl,_1bv);});}));}),_1bt[1],B(_1b7(_1bu[1]))));})],_9],_1bu[2]];}};},_1bx=new T(function(){return B(_18X(_108));}),_1by=function(_1bz){return E(E(_1bz)[1]);},_1bA=function(_1bB,_1bC){var _1bD=E(_1bB);if(!_1bD){return [0];}else{var _1bE=E(_1bC);return _1bE[0]==0?[0]:[1,_1bE[1],new T(function(){return B(_1bA(_1bD-1|0,_1bE[2]));})];}},_1bF=function(_1bG,_1bH){return _1bG<0?[0]:B(_1bA(_1bG,_1bH));},_1bI=function(_1bJ,_1bK){var _1bL=E(_1bJ)[1];return _1bL>0?B(_1bF(_1bL,_1bK)):[0];},_1bM=function(_1bN,_1bO){return [1,_,_1bN,_1bO];},_1bP=function(_1bQ){return E(E(_1bQ)[2]);},_1bR=function(_1bS){return E(E(_1bS)[4]);},_1bT=function(_1bU,_1bV,_1bW){var _1bX=E(_1bU),_1bY=E(_1bX[2]);return new F(function(){return _1au(_1bX[1],_1bY[1],_1bY[2],_1bY[3],_1bY[4],_1bY[5],_1bY[6],_1bX[3],_1bX[4],_1bV,_1bW);});},_1bZ=function(_1c0,_1c1,_1c2,_1c3,_1c4,_1c5){var _1c6=B(A(_1c2,[_1c4,_1c5]));if(!_1c6[0]){var _1c7=B(A(_1c2,[_1c5,_1c4]));if(!_1c7[0]){var _1c8=B(A(_1c0,[_1c4,_1c5]));if(!_1c8[0]){return [1,[0,new T(function(){return B(_1bR(_1c1));}),_1c4,_1c5]];}else{var _1c9=B(_1ca([0,_1c0,_1c1,_1c2,_1c3],_1c8[1]));return _1c9[0]==0?E(_1c9):[1,[2,new T(function(){return B(_1bR(_1c1));}),_1c9[1],_1c4,_1c5]];}}else{var _1cb=E(_1c7[1]);return new F(function(){return _1bT(_1cb[1],_1cb[2],_1cb[3]);});}}else{var _1cc=E(_1c6[1]);return new F(function(){return _1bT(_1cc[1],_1cc[2],_1cc[3]);});}},_1cd=function(_1ce){return E(E(_1ce)[6]);},_1ca=function(_1cf,_1cg){var _1ch=E(_1cg);if(!_1ch[0]){return E(_1at);}else{var _1ci=E(_1ch[1]),_1cj=E(_1ci[1]),_1ck=B(_1bZ(_1cj[1],_1cj[2],_1cj[3],_1cj[4],_1ci[2],_1ci[3]));if(!_1ck[0]){var _1cl=_1ck[1],_1cm=B(_1ca(_1cf,B(_7X(function(_1cn){var _1co=E(_1cn),_1cp=_1co[1];return [0,_1cp,new T(function(){return B(A(_1cd,[B(_1bP(_1cp)),_1cl,_1co[2]]));}),new T(function(){return B(A(_1cd,[B(_1bP(_1cp)),_1cl,_1co[3]]));})];},_1ch[2]))));if(!_1cm[0]){var _1cq=_1cm[1];return [0,new T(function(){var _1cr=function(_1cs){var _1ct=E(_1cs);return _1ct[0]==0?E(_1cq):[1,new T(function(){var _1cu=E(_1ct[1]),_1cv=_1cu[1];return [0,_1cv,_1cu[2],new T(function(){return B(A(_1cd,[B(_1bP(_1cv)),_1cq,_1cu[3]]));})];}),new T(function(){return B(_1cr(_1ct[2]));})];};return B(_1cr(_1cl));})];}else{return [1,new T(function(){return B(_1bM(_1cf,_1cm[1]));})];}}else{return [1,[1,_,_1cj,_1ck[1]]];}}},_1cw=function(_1cx,_1cy,_1cz,_1cA,_1cB,_1cC,_1cD,_1cE,_1cF,_1cG,_1cH,_1cI){var _1cJ=new T(function(){return B(_1aQ(_1cI));}),_1cK=function(_1cL,_1cM){return new F(function(){return _af(_1cD,_1cC,_1cB,_1cz,_1cA,_1cx,_1cy,_1cL);});},_1cN=new T(function(){return B(_16x(_1bx,_14u,new T(function(){return B(_16q(_1cK));}),new T(function(){return B(_17B(_1cK));}),_1cD,_1cC,_1cB,_1cA,_1cz,_1cx,_1cy));}),_1cO=function(_1cP,_1cQ){return new F(function(){return _17I(_1cH,_1cF,_1cG,_1cA,_1cD,_1cz,_1cC,_1cB,_1cx,_1cy,_1cP,_1cQ);});};return function(_1cR,_1cS,_1cT){var _1cU=new T(function(){return B(A(_1cE,[_1cT]));});return [0,new T(function(){return B(_19k(function(_1cV,_1cW){var _1cX=B(A(new T(function(){return B(_1bj(_1cx,_1cy,_1cz,_1cA,_1cB,_1cC,_1cD));}),[new T(function(){var _1cY=E(E(_1cW)[1]);if(!_1cY[0]){var _1cZ=[0];}else{var _1d0=E(_1cY[1]),_1cZ=_1d0[0]==0?[0]:[1,new T(function(){var _1d1=E(_1d0[1]);return _1d1[0]==0?E(_1aP):B(_10y(new T(function(){var _1d2=E(B(A(_1cJ,[_1cR]))[2]);if(!_1d2[0]){var _1d3=E(_1b3);}else{var _1d4=E(_1d2[1]);if(!_1d4[0]){var _1d5=E(_1b3);}else{var _1d6=_1d4[1];if(!E(_1d4[2])[0]){var _1d7=B(_16W(_1cO,_1cN,_1d6,_1cU));if(!_1d7[0]){var _1d8=B(_16W(_1cO,_1cN,_1cU,_1d6));if(!_1d8[0]){var _1d9=B(_1cO(_1d6,_1cU));if(!_1d9[0]){var _1da=[0];}else{var _1db=B(_1ca([0,_1cO,_1cN,function(_1dc,_1dd){return new F(function(){return _16W(_1cO,_1cN,_1dc,_1dd);});},_1b4],_1d9[1])),_1da=_1db[0]==0?E(_1db[1]):[0];}var _1de=_1da;}else{var _1df=E(_1d8[1]),_1dg=E(_1df[1]),_1dh=E(_1dg[2]),_1di=B(_1au(_1dg[1],_1dh[1],_1dh[2],_1dh[3],_1dh[4],_1dh[5],_1dh[6],_1dg[3],_1dg[4],_1df[2],_1df[3])),_1de=_1di[0]==0?E(_1di[1]):[0];}var _1dj=_1de;}else{var _1dk=E(_1d7[1]),_1dl=E(_1dk[1]),_1dm=E(_1dl[2]),_1dn=B(_1au(_1dl[1],_1dm[1],_1dm[2],_1dm[3],_1dm[4],_1dm[5],_1dm[6],_1dl[3],_1dl[4],_1dk[2],_1dk[3])),_1dj=_1dn[0]==0?E(_1dn[1]):[0];}var _1do=_1dj;}else{var _1do=E(_1b3);}var _1d5=_1do;}var _1d3=_1d5;}var _1dp=_1d3;return _1dp;}),_1d1[1]));})];}var _1dq=_1cZ;return _1dq;}),_1cV])),_1dr=_1cX[2],_1ds=E(E(_1cW)[1]);if(!_1ds[0]){return E(_1aJ);}else{var _1dt=E(_1ds[1]);if(!_1dt[0]){return E(_1ds[2])[0]==0?E(_1cX):E(_1aJ);}else{var _1du=E(_1cX[1]);if(!_1du[0]){return [0,_9,_1dr];}else{var _1dv=E(_1du[1]);if(!_1dv[0]){return E(_1cX);}else{var _1dw=_1dv[1],_1dx=new T(function(){return [0,B(_16e(_1dt[1],0))];});return [0,[1,[1,new T(function(){return B(_1bI(_1dx,_1dw));})],[1,[1,new T(function(){return B(_1aX(_1dx,_1dw));})],_1du[2]]],_1dr];}}}}},_1cS,new T(function(){return B(A(new T(function(){return B(_1by(_1cI));}),[_1cR]));},1)));}),[0,new T(function(){return E(B(A(_1cJ,[_1cR]))[1]);}),[1,[1,_1cU,_9]]]];};},_1dy=function(_1dz,_1dA){return [0];},_1dB=function(_1dC,_1dD,_1dE,_1dF,_1dG,_1dH,_1dI,_1dJ,_1dK,_1dL,_1dM){var _1dN=new T(function(){return B(_1cw(_1dC,_1dD,_1dE,_1dF,_1dG,_1dH,_1dI,_1dJ,_1dK,_1dL,_1dM,_13h));}),_1dO=new T(function(){return B(_1a6(_1dM,_1dK,_1dL,_1dF,_1dI,_1dE,_1dH,_1dG,_1dC,_1dD));}),_1dP=[0,_1dO,new T(function(){return B(_130(_1bx,_14u,new T(function(){return B(_Zo(new T(function(){return B(_106(new T(function(){return B(_ZM(_1dI,_1dH,_1dG,_1dF,_1dE,_1dC,_1dD));})));})));}),new T(function(){return B(_13P(new T(function(){return B(_14i(new T(function(){return B(_b9(_1dI,_1dH,_1dG,_1dF,_1dE,_1dC,_1dD));})));})));}),_1dI,_1dH,_1dG,_1dF,_1dE,_1dC,_1dD));}),_1dy,_1];return function(_1dQ,_1dR,_1dS){var _1dT=B(_7u(function(_1dU){var _1dV=B(A(_1dO,[new T(function(){return B(A(_1dN,[_1dU,_1dR,_1dS]));}),_1dU]));return _1dV[0]==0?false:B(_1ca(_1dP,_1dV[1]))[0]==0?true:false;},E(_1dQ)[1]));if(!_1dT[0]){return [0];}else{var _1dW=_1dT[1],_1dX=new T(function(){return B(A(_1dN,[_1dW,_1dR,_1dS]));}),_1dY=B(A(_1dO,[_1dW,_1dX]));if(!_1dY[0]){return [0];}else{var _1dZ=B(_1ca(_1dP,_1dY[1]));if(!_1dZ[0]){var _1e0=_1dZ[1];return [1,new T(function(){var _1e1=E(E(_1dX)[2]);return [0,new T(function(){return B(_7X(function(_1e2){return new F(function(){return _115(_1e0,_1e2);});},_1e1[1]));}),new T(function(){return B(_115(_1e0,_1e1[2]));})];})];}else{return [0];}}}};},_1e3=[1],_1e4=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_1e5=function(_1e6){return new F(function(){return err(_1e4);});},_1e7=new T(function(){return B(_1e5(_));}),_1e8=function(_1e9,_1ea,_1eb){var _1ec=E(_1eb);if(!_1ec[0]){var _1ed=_1ec[1],_1ee=E(_1ea);if(!_1ee[0]){var _1ef=_1ee[1],_1eg=_1ee[2];if(_1ef<=(imul(3,_1ed)|0)){return [0,(1+_1ef|0)+_1ed|0,E(E(_1e9)),E(_1ee),E(_1ec)];}else{var _1eh=E(_1ee[3]);if(!_1eh[0]){var _1ei=_1eh[1],_1ej=E(_1ee[4]);if(!_1ej[0]){var _1ek=_1ej[1],_1el=_1ej[2],_1em=_1ej[3];if(_1ek>=(imul(2,_1ei)|0)){var _1en=function(_1eo){var _1ep=E(_1ej[4]);return _1ep[0]==0?[0,(1+_1ef|0)+_1ed|0,E(_1el),E([0,(1+_1ei|0)+_1eo|0,E(_1eg),E(_1eh),E(_1em)]),E([0,(1+_1ed|0)+_1ep[1]|0,E(E(_1e9)),E(_1ep),E(_1ec)])]:[0,(1+_1ef|0)+_1ed|0,E(_1el),E([0,(1+_1ei|0)+_1eo|0,E(_1eg),E(_1eh),E(_1em)]),E([0,1+_1ed|0,E(E(_1e9)),E(_1e3),E(_1ec)])];},_1eq=E(_1em);return _1eq[0]==0?B(_1en(_1eq[1])):B(_1en(0));}else{return [0,(1+_1ef|0)+_1ed|0,E(_1eg),E(_1eh),E([0,(1+_1ed|0)+_1ek|0,E(E(_1e9)),E(_1ej),E(_1ec)])];}}else{return E(_1e7);}}else{return E(_1e7);}}}else{return [0,1+_1ed|0,E(E(_1e9)),E(_1e3),E(_1ec)];}}else{var _1er=E(_1ea);if(!_1er[0]){var _1es=_1er[1],_1et=_1er[2],_1eu=_1er[4],_1ev=E(_1er[3]);if(!_1ev[0]){var _1ew=_1ev[1],_1ex=E(_1eu);if(!_1ex[0]){var _1ey=_1ex[1],_1ez=_1ex[2],_1eA=_1ex[3];if(_1ey>=(imul(2,_1ew)|0)){var _1eB=function(_1eC){var _1eD=E(_1ex[4]);return _1eD[0]==0?[0,1+_1es|0,E(_1ez),E([0,(1+_1ew|0)+_1eC|0,E(_1et),E(_1ev),E(_1eA)]),E([0,1+_1eD[1]|0,E(E(_1e9)),E(_1eD),E(_1e3)])]:[0,1+_1es|0,E(_1ez),E([0,(1+_1ew|0)+_1eC|0,E(_1et),E(_1ev),E(_1eA)]),E([0,1,E(E(_1e9)),E(_1e3),E(_1e3)])];},_1eE=E(_1eA);return _1eE[0]==0?B(_1eB(_1eE[1])):B(_1eB(0));}else{return [0,1+_1es|0,E(_1et),E(_1ev),E([0,1+_1ey|0,E(E(_1e9)),E(_1ex),E(_1e3)])];}}else{return [0,3,E(_1et),E(_1ev),E([0,1,E(E(_1e9)),E(_1e3),E(_1e3)])];}}else{var _1eF=E(_1eu);return _1eF[0]==0?[0,3,E(_1eF[2]),E([0,1,E(_1et),E(_1e3),E(_1e3)]),E([0,1,E(E(_1e9)),E(_1e3),E(_1e3)])]:[0,2,E(E(_1e9)),E(_1er),E(_1e3)];}}else{return [0,1,E(E(_1e9)),E(_1e3),E(_1e3)];}}},_1eG=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_1eH=function(_1eI){return new F(function(){return err(_1eG);});},_1eJ=new T(function(){return B(_1eH(_));}),_1eK=function(_1eL,_1eM,_1eN){var _1eO=E(_1eM);if(!_1eO[0]){var _1eP=_1eO[1],_1eQ=E(_1eN);if(!_1eQ[0]){var _1eR=_1eQ[1],_1eS=_1eQ[2];if(_1eR<=(imul(3,_1eP)|0)){return [0,(1+_1eP|0)+_1eR|0,E(E(_1eL)),E(_1eO),E(_1eQ)];}else{var _1eT=E(_1eQ[3]);if(!_1eT[0]){var _1eU=_1eT[1],_1eV=_1eT[2],_1eW=_1eT[3],_1eX=E(_1eQ[4]);if(!_1eX[0]){var _1eY=_1eX[1];if(_1eU>=(imul(2,_1eY)|0)){var _1eZ=function(_1f0){var _1f1=E(_1eL),_1f2=E(_1eT[4]);return _1f2[0]==0?[0,(1+_1eP|0)+_1eR|0,E(_1eV),E([0,(1+_1eP|0)+_1f0|0,E(_1f1),E(_1eO),E(_1eW)]),E([0,(1+_1eY|0)+_1f2[1]|0,E(_1eS),E(_1f2),E(_1eX)])]:[0,(1+_1eP|0)+_1eR|0,E(_1eV),E([0,(1+_1eP|0)+_1f0|0,E(_1f1),E(_1eO),E(_1eW)]),E([0,1+_1eY|0,E(_1eS),E(_1e3),E(_1eX)])];},_1f3=E(_1eW);return _1f3[0]==0?B(_1eZ(_1f3[1])):B(_1eZ(0));}else{return [0,(1+_1eP|0)+_1eR|0,E(_1eS),E([0,(1+_1eP|0)+_1eU|0,E(E(_1eL)),E(_1eO),E(_1eT)]),E(_1eX)];}}else{return E(_1eJ);}}else{return E(_1eJ);}}}else{return [0,1+_1eP|0,E(E(_1eL)),E(_1eO),E(_1e3)];}}else{var _1f4=E(_1eN);if(!_1f4[0]){var _1f5=_1f4[1],_1f6=_1f4[2],_1f7=_1f4[4],_1f8=E(_1f4[3]);if(!_1f8[0]){var _1f9=_1f8[1],_1fa=_1f8[2],_1fb=_1f8[3],_1fc=E(_1f7);if(!_1fc[0]){var _1fd=_1fc[1];if(_1f9>=(imul(2,_1fd)|0)){var _1fe=function(_1ff){var _1fg=E(_1eL),_1fh=E(_1f8[4]);return _1fh[0]==0?[0,1+_1f5|0,E(_1fa),E([0,1+_1ff|0,E(_1fg),E(_1e3),E(_1fb)]),E([0,(1+_1fd|0)+_1fh[1]|0,E(_1f6),E(_1fh),E(_1fc)])]:[0,1+_1f5|0,E(_1fa),E([0,1+_1ff|0,E(_1fg),E(_1e3),E(_1fb)]),E([0,1+_1fd|0,E(_1f6),E(_1e3),E(_1fc)])];},_1fi=E(_1fb);return _1fi[0]==0?B(_1fe(_1fi[1])):B(_1fe(0));}else{return [0,1+_1f5|0,E(_1f6),E([0,1+_1f9|0,E(E(_1eL)),E(_1e3),E(_1f8)]),E(_1fc)];}}else{return [0,3,E(_1fa),E([0,1,E(E(_1eL)),E(_1e3),E(_1e3)]),E([0,1,E(_1f6),E(_1e3),E(_1e3)])];}}else{var _1fj=E(_1f7);return _1fj[0]==0?[0,3,E(_1f6),E([0,1,E(E(_1eL)),E(_1e3),E(_1e3)]),E(_1fj)]:[0,2,E(E(_1eL)),E(_1e3),E(_1f4)];}}else{return [0,1,E(E(_1eL)),E(_1e3),E(_1e3)];}}},_1fk=function(_1fl){return [0,1,E(E(_1fl)),E(_1e3),E(_1e3)];},_1fm=function(_1fn,_1fo){var _1fp=E(_1fo);if(!_1fp[0]){return new F(function(){return _1e8(_1fp[2],B(_1fm(_1fn,_1fp[3])),_1fp[4]);});}else{return new F(function(){return _1fk(_1fn);});}},_1fq=function(_1fr,_1fs){var _1ft=E(_1fs);if(!_1ft[0]){return new F(function(){return _1eK(_1ft[2],_1ft[3],B(_1fq(_1fr,_1ft[4])));});}else{return new F(function(){return _1fk(_1fr);});}},_1fu=function(_1fv,_1fw,_1fx,_1fy,_1fz){return new F(function(){return _1eK(_1fx,_1fy,B(_1fq(_1fv,_1fz)));});},_1fA=function(_1fB,_1fC,_1fD,_1fE,_1fF){return new F(function(){return _1e8(_1fD,B(_1fm(_1fB,_1fE)),_1fF);});},_1fG=function(_1fH,_1fI,_1fJ,_1fK,_1fL,_1fM){var _1fN=E(_1fI);if(!_1fN[0]){var _1fO=_1fN[1],_1fP=_1fN[2],_1fQ=_1fN[3],_1fR=_1fN[4];if((imul(3,_1fO)|0)>=_1fJ){if((imul(3,_1fJ)|0)>=_1fO){return [0,(_1fO+_1fJ|0)+1|0,E(E(_1fH)),E(_1fN),E([0,_1fJ,E(_1fK),E(_1fL),E(_1fM)])];}else{return new F(function(){return _1eK(_1fP,_1fQ,B(_1fG(_1fH,_1fR,_1fJ,_1fK,_1fL,_1fM)));});}}else{return new F(function(){return _1e8(_1fK,B(_1fS(_1fH,_1fO,_1fP,_1fQ,_1fR,_1fL)),_1fM);});}}else{return new F(function(){return _1fA(_1fH,_1fJ,_1fK,_1fL,_1fM);});}},_1fS=function(_1fT,_1fU,_1fV,_1fW,_1fX,_1fY){var _1fZ=E(_1fY);if(!_1fZ[0]){var _1g0=_1fZ[1],_1g1=_1fZ[2],_1g2=_1fZ[3],_1g3=_1fZ[4];if((imul(3,_1fU)|0)>=_1g0){if((imul(3,_1g0)|0)>=_1fU){return [0,(_1fU+_1g0|0)+1|0,E(E(_1fT)),E([0,_1fU,E(_1fV),E(_1fW),E(_1fX)]),E(_1fZ)];}else{return new F(function(){return _1eK(_1fV,_1fW,B(_1fG(_1fT,_1fX,_1g0,_1g1,_1g2,_1g3)));});}}else{return new F(function(){return _1e8(_1g1,B(_1fS(_1fT,_1fU,_1fV,_1fW,_1fX,_1g2)),_1g3);});}}else{return new F(function(){return _1fu(_1fT,_1fU,_1fV,_1fW,_1fX);});}},_1g4=function(_1g5,_1g6,_1g7){var _1g8=E(_1g6);if(!_1g8[0]){var _1g9=_1g8[1],_1ga=_1g8[2],_1gb=_1g8[3],_1gc=_1g8[4],_1gd=E(_1g7);if(!_1gd[0]){var _1ge=_1gd[1],_1gf=_1gd[2],_1gg=_1gd[3],_1gh=_1gd[4];if((imul(3,_1g9)|0)>=_1ge){if((imul(3,_1ge)|0)>=_1g9){return [0,(_1g9+_1ge|0)+1|0,E(E(_1g5)),E(_1g8),E(_1gd)];}else{return new F(function(){return _1eK(_1ga,_1gb,B(_1fG(_1g5,_1gc,_1ge,_1gf,_1gg,_1gh)));});}}else{return new F(function(){return _1e8(_1gf,B(_1fS(_1g5,_1g9,_1ga,_1gb,_1gc,_1gg)),_1gh);});}}else{return new F(function(){return _1fu(_1g5,_1g9,_1ga,_1gb,_1gc);});}}else{return new F(function(){return _1fm(_1g5,_1g7);});}},_1gi=function(_1gj,_1gk,_1gl,_1gm){var _1gn=E(_1gm);if(!_1gn[0]){var _1go=new T(function(){var _1gp=B(_1gi(_1gn[1],_1gn[2],_1gn[3],_1gn[4]));return [0,_1gp[1],_1gp[2]];});return [0,new T(function(){return E(E(_1go)[1]);}),new T(function(){return B(_1e8(_1gk,_1gl,E(_1go)[2]));})];}else{return [0,_1gk,_1gl];}},_1gq=function(_1gr,_1gs,_1gt,_1gu){var _1gv=E(_1gt);if(!_1gv[0]){var _1gw=new T(function(){var _1gx=B(_1gq(_1gv[1],_1gv[2],_1gv[3],_1gv[4]));return [0,_1gx[1],_1gx[2]];});return [0,new T(function(){return E(E(_1gw)[1]);}),new T(function(){return B(_1eK(_1gs,E(_1gw)[2],_1gu));})];}else{return [0,_1gs,_1gu];}},_1gy=function(_1gz,_1gA){var _1gB=E(_1gz);if(!_1gB[0]){var _1gC=_1gB[1],_1gD=E(_1gA);if(!_1gD[0]){var _1gE=_1gD[1];if(_1gC<=_1gE){var _1gF=B(_1gq(_1gE,_1gD[2],_1gD[3],_1gD[4]));return new F(function(){return _1e8(_1gF[1],_1gB,_1gF[2]);});}else{var _1gG=B(_1gi(_1gC,_1gB[2],_1gB[3],_1gB[4]));return new F(function(){return _1eK(_1gG[1],_1gG[2],_1gD);});}}else{return E(_1gB);}}else{return E(_1gA);}},_1gH=function(_1gI,_1gJ,_1gK,_1gL,_1gM){var _1gN=E(_1gI);if(!_1gN[0]){var _1gO=_1gN[1],_1gP=_1gN[2],_1gQ=_1gN[3],_1gR=_1gN[4];if((imul(3,_1gO)|0)>=_1gJ){if((imul(3,_1gJ)|0)>=_1gO){return new F(function(){return _1gy(_1gN,[0,_1gJ,E(_1gK),E(_1gL),E(_1gM)]);});}else{return new F(function(){return _1eK(_1gP,_1gQ,B(_1gH(_1gR,_1gJ,_1gK,_1gL,_1gM)));});}}else{return new F(function(){return _1e8(_1gK,B(_1gS(_1gO,_1gP,_1gQ,_1gR,_1gL)),_1gM);});}}else{return [0,_1gJ,E(_1gK),E(_1gL),E(_1gM)];}},_1gS=function(_1gT,_1gU,_1gV,_1gW,_1gX){var _1gY=E(_1gX);if(!_1gY[0]){var _1gZ=_1gY[1],_1h0=_1gY[2],_1h1=_1gY[3],_1h2=_1gY[4];if((imul(3,_1gT)|0)>=_1gZ){if((imul(3,_1gZ)|0)>=_1gT){return new F(function(){return _1gy([0,_1gT,E(_1gU),E(_1gV),E(_1gW)],_1gY);});}else{return new F(function(){return _1eK(_1gU,_1gV,B(_1gH(_1gW,_1gZ,_1h0,_1h1,_1h2)));});}}else{return new F(function(){return _1e8(_1h0,B(_1gS(_1gT,_1gU,_1gV,_1gW,_1h1)),_1h2);});}}else{return [0,_1gT,E(_1gU),E(_1gV),E(_1gW)];}},_1h3=function(_1h4,_1h5){var _1h6=E(_1h4);if(!_1h6[0]){var _1h7=_1h6[1],_1h8=_1h6[2],_1h9=_1h6[3],_1ha=_1h6[4],_1hb=E(_1h5);if(!_1hb[0]){var _1hc=_1hb[1],_1hd=_1hb[2],_1he=_1hb[3],_1hf=_1hb[4];if((imul(3,_1h7)|0)>=_1hc){if((imul(3,_1hc)|0)>=_1h7){return new F(function(){return _1gy(_1h6,_1hb);});}else{return new F(function(){return _1eK(_1h8,_1h9,B(_1gH(_1ha,_1hc,_1hd,_1he,_1hf)));});}}else{return new F(function(){return _1e8(_1hd,B(_1gS(_1h7,_1h8,_1h9,_1ha,_1he)),_1hf);});}}else{return E(_1h6);}}else{return E(_1h5);}},_1hg=function(_1hh,_1hi){var _1hj=E(_1hi);if(!_1hj[0]){var _1hk=_1hj[2],_1hl=_1hj[3],_1hm=_1hj[4];if(!B(A(_1hh,[_1hk]))){return new F(function(){return _1h3(B(_1hg(_1hh,_1hl)),B(_1hg(_1hh,_1hm)));});}else{return new F(function(){return _1g4(_1hk,B(_1hg(_1hh,_1hl)),B(_1hg(_1hh,_1hm)));});}}else{return [1];}},_1hn=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_1ho=new T(function(){return B(err(_1hn));}),_1hp=function(_1hq,_1hr,_1hs,_1ht){while(1){var _1hu=E(_1hs);if(!_1hu[0]){_1hq=_1hu[1];_1hr=_1hu[2];_1hs=_1hu[3];_1ht=_1hu[4];continue;}else{return E(_1hr);}}},_1hv=function(_1hw,_1hx){var _1hy=B(_1hg(function(_1hz){return new F(function(){return _l0(E(_1hz)[2],_1hw);});},_1hx));if(!_1hy[0]){var _1hA=E(_1hy[3]);return _1hA[0]==0?B(_1hp(_1hA[1],_1hA[2],_1hA[3],_1hA[4])):E(_1hy[2]);}else{return E(_1ho);}},_1hB=[1,_9],_1hC=function(_1hD,_1hE,_1hF,_1hG,_1hH,_1hI,_1hJ,_1hK,_1hL,_1hM,_1hN,_1hO,_1hP,_1hQ){var _1hR=E(_1hQ);if(!_1hR[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_1hK,[_1hP]));}),_9]],_9],[1,[1,new T(function(){return B(A(_1hK,[_1hP]));}),_9]]]];}else{var _1hS=function(_1hT){var _1hU=E(_1hT);if(!_1hU[0]){return E(_1hB);}else{var _1hV=E(_1hU[1]),_1hW=B(_1hC(_1hD,_1hE,_1hF,_1hG,_1hH,_1hI,_1hJ,_1hK,_1hL,_1hM,_1hN,_1hO,_1hV[1],_1hV[2]));if(!_1hW[0]){return [0];}else{var _1hX=B(_1hS(_1hU[2]));return _1hX[0]==0?[0]:[1,[1,_1hW[1],_1hX[1]]];}}},_1hY=B(_1hS(_1hR[2]));return _1hY[0]==0?[0]:B(A(_1dB,[_1hD,_1hE,_1hF,_1hG,_1hH,_1hI,_1hJ,_1hK,_1hL,_1hM,_1hN,new T(function(){return B(_1hv(_1hR[1],_1hO));}),_1hY[1],_1hP]));}},_1hZ=function(_1i0,_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,_1i7,_1i8,_1i9,_1ia,_1ib,_1ic,_1id,_1ie){var _1if=E(_1ie);return new F(function(){return _1hC(_1i0,_1i1,_1i2,_1i3,_1i4,_1i5,_1i6,_1i7,_1i8,_1ib,_1ic,_1id,_1if[1],_1if[2]);});},_1ig=new T(function(){return B(unCStr("div"));}),_1ih=function(_1ii,_1ij,_1ik,_){var _1il=jsCreateElem(toJSStr(E(_1ig))),_1im=_1il,_1in=jsAppendChild(_1im,E(_1ik)[1]),_1io=[0,_1im],_1ip=B(A(_1ii,[_1ij,_1io,_])),_1iq=_1ip;return _1io;},_1ir=function(_1is){return new F(function(){return _cS(_1is,_9);});},_1it=function(_1iu,_1iv){return _1iu<=B(_16e(_1iv,0))?[1,new T(function(){var _1iw=_1iu-1|0;if(_1iw>=0){var _1ix=B(_g6(B(_1ir(_1iv)),_1iw));}else{var _1ix=E(_g3);}var _1iy=_1ix,_1iz=_1iy;return _1iz;})]:[0];},_1iA=function(_1iB,_1iC,_1iD){var _1iE=function(_1iF){return _1iF<=B(_16e(_1iD,0))?[1,[0,new T(function(){var _1iG=_1iB-1|0;if(_1iG>=0){var _1iH=B(_g6(B(_1ir(_1iD)),_1iG));}else{var _1iH=E(_g3);}var _1iI=_1iH,_1iJ=_1iI;return _1iJ;}),new T(function(){var _1iK=_1iC-1|0;if(_1iK>=0){var _1iL=B(_g6(B(_1ir(_1iD)),_1iK));}else{var _1iL=E(_g3);}var _1iM=_1iL,_1iN=_1iM;return _1iN;})]]:[0];};return _1iB>_1iC?B(_1iE(_1iB)):B(_1iE(_1iC));},_1iO=[0],_1iP=new T(function(){return B(unCStr("depends on unjustified lines"));}),_1iQ=new T(function(){return B(unCStr("unavailable lines"));}),_1iR=new T(function(){return B(unCStr("wrong number of premises"));}),_1iS=new T(function(){return B(unCStr("Impossible Error 1"));}),_1iT=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_1iU=new T(function(){return B(unCStr("PR"));}),_1iV=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_1iW=function(_1iX,_1iY,_1iZ,_1j0,_1j1,_1j2){var _1j3=function(_1j4){var _1j5=B(A(_1j0,[_1iY]));if(!_1j5[0]){return [0,[1,_1iV,_1j1],[1,_28,_1j2]];}else{var _1j6=E(_1j5[1]);if(!_1j6[0]){switch(E(E(_1j6[1])[1])){case 1:var _1j7=E(_1iZ);if(!_1j7[0]){return [0,[1,_1iR,_1j1],[1,_28,_1j2]];}else{if(!E(_1j7[2])[0]){var _1j8=B(_1it(E(_1j7[1])[1],_1j2));if(!_1j8[0]){return [0,[1,_1iQ,_1j1],[1,_28,_1j2]];}else{var _1j9=E(_1j8[1]);return _1j9[0]==0?[0,[1,_1iP,_1j1],[1,_28,_1j2]]:[0,[1,_9,_1j1],[1,[1,[0,_1iX,[1,_1iY,[1,_1j9[1],_9]]]],_1j2]];}}else{return [0,[1,_1iR,_1j1],[1,_28,_1j2]];}}break;case 2:var _1ja=E(_1iZ);if(!_1ja[0]){return [0,[1,_1iR,_1j1],[1,_28,_1j2]];}else{var _1jb=E(_1ja[2]);if(!_1jb[0]){return [0,[1,_1iR,_1j1],[1,_28,_1j2]];}else{if(!E(_1jb[2])[0]){var _1jc=B(_1iA(E(_1ja[1])[1],E(_1jb[1])[1],_1j2));if(!_1jc[0]){return [0,[1,_1iQ,_1j1],[1,_28,_1j2]];}else{var _1jd=E(_1jc[1]),_1je=E(_1jd[1]);if(!_1je[0]){return [0,[1,_1iP,_1j1],[1,_28,_1j2]];}else{var _1jf=E(_1jd[2]);return _1jf[0]==0?[0,[1,_1iP,_1j1],[1,_28,_1j2]]:[0,[1,_9,_1j1],[1,[1,[0,_1iX,[1,_1iY,[1,_1je[1],[1,_1jf[1],_9]]]]],_1j2]];}}}else{return [0,[1,_1iR,_1j1],[1,_28,_1j2]];}}}break;default:return [0,[1,_1iS,_1j1],[1,_28,_1j2]];}}else{return [0,[1,_1iT,_1j1],[1,_28,_1j2]];}}};return !B(_l0(_1iY,_1iU))?B(_1j3(_)):E(_1iZ)[0]==0?[0,[1,_9,_1j1],[1,[1,[0,_1iX,_1iO]],_1j2]]:B(_1j3(_));},_1jg=new T(function(){return B(unCStr("depends on an unjustified line"));}),_1jh=new T(function(){return B(unCStr("unavailable line"));}),_1ji=function(_1jj,_1jk,_1jl,_1jm){return E(B(_1jn(_1jj,_1jk,[1,_9,_1jl],[1,_28,_1jm]))[2]);},_1jo=function(_1jp,_1jq,_1jr,_1js,_1jt,_1ju,_1jv,_1jw){var _1jx=B(_1iA(_1js,_1jt,B(_1ji(_1jp,_1jq,_1jv,_1jw))));if(!_1jx[0]){return new F(function(){return _1jn(_1jp,_1jq,[1,_1jh,_1jv],[1,_28,_1jw]);});}else{var _1jy=E(_1jx[1]),_1jz=E(_1jy[1]);if(!_1jz[0]){return new F(function(){return _1jn(_1jp,_1jq,[1,_1jg,_1jv],[1,_28,_1jw]);});}else{var _1jA=E(_1jy[2]);return _1jA[0]==0?B(_1jn(_1jp,_1jq,[1,_1jg,_1jv],[1,_28,_1jw])):B(_1jn(_1jp,_1jq,[1,_9,_1jv],[1,[1,[0,_1jr,[1,_1ju,[1,_1jz[1],[1,_1jA[1],_9]]]]],_1jw]));}}},_1jB=new T(function(){return B(unCStr("wrong number of lines cited"));}),_1jC=function(_1jD,_1jE,_1jF,_1jG,_1jH,_1jI,_1jJ){var _1jK=E(_1jH);if(!_1jK[0]){return new F(function(){return _1jn(_1jD,_1jE,[1,_1jB,_1jI],[1,_28,_1jJ]);});}else{var _1jL=E(_1jK[2]);if(!_1jL[0]){return new F(function(){return _1jn(_1jD,_1jE,[1,_1jB,_1jI],[1,_28,_1jJ]);});}else{if(!E(_1jL[2])[0]){return new F(function(){return _1jo(_1jD,_1jE,_1jF,E(_1jK[1])[1],E(_1jL[1])[1],_1jG,_1jI,_1jJ);});}else{return new F(function(){return _1jn(_1jD,_1jE,[1,_1jB,_1jI],[1,_28,_1jJ]);});}}}},_1jM=function(_1jN,_1jO,_1jP){return [0,[1,_9,_1jO],[1,_28,new T(function(){var _1jQ=B(_16e(_1jO,0))-E(_1jN)[1]|0,_1jR=new T(function(){return _1jQ>=0?B(_1aS(_1jQ,_1jP)):E(_1jP);});if(_1jQ>0){var _1jS=function(_1jT,_1jU){var _1jV=E(_1jT);return _1jV[0]==0?E(_1jR):_1jU>1?[1,_28,new T(function(){return B(_1jS(_1jV[2],_1jU-1|0));})]:E([1,_28,_1jR]);},_1jW=B(_1jS(_1jP,_1jQ));}else{var _1jW=E(_1jR);}var _1jX=_1jW,_1jY=_1jX,_1jZ=_1jY,_1k0=_1jZ;return _1k0;})]];},_1k1=function(_1k2,_1k3,_1k4,_1k5,_1k6,_1k7,_1k8){var _1k9=new T(function(){return E(B(_1jn(_1k2,_1k3,[1,_9,_1k7],[1,_28,_1k8]))[2]);});if(_1k5<=B(_16e(_1k9,0))){var _1ka=_1k5-1|0;if(_1ka>=0){var _1kb=B(_g6(B(_1ir(_1k9)),_1ka));return _1kb[0]==0?B(_1jn(_1k2,_1k3,[1,_1jg,_1k7],[1,_28,_1k8])):B(_1jn(_1k2,_1k3,[1,_9,_1k7],[1,[1,[0,_1k4,[1,_1k6,[1,_1kb[1],_9]]]],_1k8]));}else{return E(_g3);}}else{return new F(function(){return _1jn(_1k2,_1k3,[1,_1jh,_1k7],[1,_28,_1k8]);});}},_1kc=function(_1kd,_1ke,_1kf,_1kg,_1kh,_1ki,_1kj){var _1kk=E(_1kh);if(!_1kk[0]){return new F(function(){return _1jn(_1kd,_1ke,[1,_1jB,_1ki],[1,_28,_1kj]);});}else{if(!E(_1kk[2])[0]){return new F(function(){return _1k1(_1kd,_1ke,_1kf,E(_1kk[1])[1],_1kg,_1ki,_1kj);});}else{return new F(function(){return _1jn(_1kd,_1ke,[1,_1jB,_1ki],[1,_28,_1kj]);});}}},_1kl=new T(function(){return B(unCStr("Open Subproof"));}),_1km=new T(function(){return B(unCStr("Impossible Error 2"));}),_1kn=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_1ko=new T(function(){return B(unCStr("SHOW"));}),_1kp=function(_1kq,_1kr,_1ks,_1kt,_1ku,_1kv,_1kw){if(!B(_l0(_1kr,_1ko))){var _1kx=B(A(_1kt,[_1kr]));if(!_1kx[0]){return [0,[1,_1iV,_1kv],[1,_28,_1kw]];}else{var _1ky=E(_1kx[1]);if(!_1ky[0]){return [0,[1,_1kn,_1kv],[1,_28,_1kw]];}else{switch(E(E(_1ky[1])[1])){case 1:var _1kz=B(_1kc(_1ku,_1kt,_1kq,_1kr,_1ks,_1kv,_1kw));return new F(function(){return _1jM(new T(function(){return [0,B(_16e(_1kv,0))+1|0];},1),_1kz[1],_1kz[2]);});break;case 2:var _1kA=B(_1jC(_1ku,_1kt,_1kq,_1kr,_1ks,_1kv,_1kw));return new F(function(){return _1jM(new T(function(){return [0,B(_16e(_1kv,0))+1|0];},1),_1kA[1],_1kA[2]);});break;default:return [0,[1,_1km,_1kv],[1,_28,_1kw]];}}}}else{var _1kB=B(_1jn(_1ku,_1kt,[1,_1kl,_1kv],[1,_28,_1kw]));return new F(function(){return _1jM(new T(function(){return [0,B(_16e(_1kv,0))+1|0];},1),_1kB[1],_1kB[2]);});}},_1kC=new T(function(){return B(unCStr("shouldn\'t happen"));}),_1kD=new T(function(){return B(unCStr("incomplete line"));}),_1kE=function(_1kF,_1kG,_1kH,_1kI,_1kJ){var _1kK=E(_1kF);if(!_1kK[0]){return E(_1kG)[0]==0?[0,[1,_1kD,_1kI],[1,_28,_1kJ]]:[0,[1,_1kC,_1kI],[1,_28,_1kJ]];}else{var _1kL=_1kK[1],_1kM=E(_1kG);if(!_1kM[0]){var _1kN=E(_1kL);return new F(function(){return _1iW(_1kN[1],_1kN[2],_1kN[3],_1kH,_1kI,_1kJ);});}else{var _1kO=E(_1kL);return new F(function(){return _1kp(_1kO[1],_1kO[2],_1kO[3],_1kH,_1kM,_1kI,_1kJ);});}}},_1jn=function(_1kP,_1kQ,_1kR,_1kS){return new F(function(){return (function(_1kT,_1kU,_1kV){while(1){var _1kW=E(_1kV);if(!_1kW[0]){return [0,_1kT,_1kU];}else{var _1kX=E(_1kW[1]),_1kY=B(_1kE(_1kX[1],_1kX[2],_1kQ,_1kT,_1kU));_1kT=_1kY[1];_1kU=_1kY[2];_1kV=_1kW[2];continue;}}})(_1kR,_1kS,_1kP);});},_1kZ=function(_1l0,_1l1){while(1){var _1l2=E(_1l1);if(!_1l2[0]){return true;}else{if(!B(A(_1l0,[_1l2[1]]))){return false;}else{_1l1=_1l2[2];continue;}}}},_1l3=[0,666],_1l4=[0,_,_1l3],_1l5=[1,_1l4],_1l6=[0,_1l5,_1iO],_1l7=function(_1l8){return new F(function(){return _l0(_1l8,_9);});},_1l9=function(_1la,_1lb){var _1lc=B(_1jn(_1la,_1lb,_9,_9)),_1ld=_1lc[1];return !B(_1kZ(_1l7,_1ld))?[0,_1ld]:[1,new T(function(){var _1le=B(_16e(_1la,0))-1|0;if(_1le>=0){var _1lf=B(_g6(B(_cS(_1lc[2],_9)),_1le)),_1lg=_1lf[0]==0?E(_1l6):E(_1lf[1]);}else{var _1lg=E(_g3);}var _1lh=_1lg,_1li=_1lh,_1lj=_1li;return _1lj;})];},_1lk=function(_1ll,_){return _1ll;},_1lm=function(_1ln){var _1lo=E(_1ln);return _1lo[0]==0?E(_1lk):function(_1lp,_){var _1lq=B(A(new T(function(){var _1lr=E(_1lo[1]);return B(_1ls(_1lr[1],_1lr[2]));}),[_1lp,_])),_1lt=_1lq,_1lu=B(A(new T(function(){return B(_1lm(_1lo[2]));}),[_1lp,_])),_1lv=_1lu;return _1lp;};},_1lw=function(_1lx,_1ly){return function(_1lz,_){var _1lA=B(A(new T(function(){var _1lB=E(_1lx);return B(_1ls(_1lB[1],_1lB[2]));}),[_1lz,_])),_1lC=_1lA,_1lD=B(A(new T(function(){return B(_1lm(_1ly));}),[_1lz,_])),_1lE=_1lD;return _1lz;};},_1lF=function(_1lG,_1lH){return new F(function(){return _F(0,E(_1lG)[1],_1lH);});},_1lI=function(_1lJ){return function(_lH,_19h){return new F(function(){return _56(new T(function(){return B(_2T(_1lF,_1lJ,_9));}),_lH,_19h);});};},_1lK=function(_1lL){return function(_lH,_19h){return new F(function(){return _56(new T(function(){return B(_Un(_Q,_u,_Q,_N,_Q,_Ud,_1lL,_UB));}),_lH,_19h);});};},_1lM=new T(function(){return B(unCStr("open"));}),_1lN=new T(function(){return B(unCStr("termination"));}),_1lO=new T(function(){return B(unCStr("closed"));}),_1lP=function(_1lQ){var _1lR=E(_1lQ);return _1lR[0]==0?E(_1lk):function(_1lS,_){var _1lT=B(A(new T(function(){var _1lU=E(_1lR[1]);return B(_1ls(_1lU[1],_1lU[2]));}),[_1lS,_])),_1lV=_1lT,_1lW=B(A(new T(function(){return B(_1lP(_1lR[2]));}),[_1lS,_])),_1lX=_1lW;return _1lS;};},_1lY=function(_1lZ,_1m0){return function(_1m1,_){var _1m2=B(A(new T(function(){var _1m3=E(_1lZ);return B(_1ls(_1m3[1],_1m3[2]));}),[_1m1,_])),_1m4=_1m2,_1m5=B(A(new T(function(){return B(_1lP(_1m0));}),[_1m1,_])),_1m6=_1m5;return _1m1;};},_1m7=new T(function(){return B(unCStr("SHOW"));}),_1ls=function(_1m8,_1m9){var _1ma=E(_1m8);if(!_1ma[0]){return function(_lH,_19h){return new F(function(){return _1ih(_56,_1ma[1],_lH,_19h);});};}else{var _1mb=E(_1ma[1]),_1mc=_1mb[1],_1md=_1mb[2],_1me=_1mb[3];if(!B(_l0(_1md,_1m7))){var _1mf=E(_1m9);return _1mf[0]==0?function(_lH,_19h){return new F(function(){return _1ih(_63,function(_1mg,_){var _1mh=B(_5T(_1lK,_1mc,_1mg,_)),_1mi=_1mh,_1mj=B(_5T(_63,function(_1mk,_){var _1ml=B(_5T(_56,_1md,_1mk,_)),_1mm=_1ml,_1mn=B(_5T(_1lI,_1me,_1mk,_)),_1mo=_1mn;return _1mk;},_1mg,_)),_1mp=_1mj;return _1mg;},_lH,_19h);});}:function(_lH,_19h){return new F(function(){return _1ih(_63,function(_1mq,_){var _1mr=B(_5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_Un(_Q,_u,_Q,_N,_Q,_Ud,_1mc,_UB));})));}),_1mq,_)),_1ms=_1mr,_1mt=B(_1ih(_63,function(_1mu,_){var _1mv=B(_5T(_63,new T(function(){return B(_1lw(_1mf[1],_1mf[2]));}),_1mu,_)),_1mw=_1mv,_1mx=B(_1ih(_63,function(_1my,_){var _1mz=B(_5T(_56,_9,_1my,_)),_1mA=_1mz,_1mB=B(A(_5d,[_5q,_1mA,_bP,_1lN,_])),_1mC=_1mB,_1mD=B(_5T(_63,function(_1mE,_){var _1mF=B(_5T(_56,_1md,_1mE,_)),_1mG=_1mF,_1mH=B(_5T(_1lI,_1me,_1mE,_)),_1mI=_1mH;return _1mE;},_1my,_)),_1mJ=_1mD;return _1my;},_1mu,_)),_1mK=_1mx;return _1mu;},_1mq,_)),_1mL=_1mt,_1mM=B(A(_5d,[_5q,_1mL,_bP,_1lO,_])),_1mN=_1mM;return _1mq;},_lH,_19h);});};}else{var _1mO=E(_1m9);return _1mO[0]==0?function(_lH,_19h){return new F(function(){return _1ih(_63,function(_bC,_){return new F(function(){return _5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_Un(_Q,_u,_Q,_N,_Q,_Ud,_1mc,_UB));})));}),_bC,_);});},_lH,_19h);});}:function(_lH,_19h){return new F(function(){return _1ih(_63,function(_1mP,_){var _1mQ=B(_5T(_56,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_Un(_Q,_u,_Q,_N,_Q,_Ud,_1mc,_UB));})));}),_1mP,_)),_1mR=_1mQ,_1mS=B(_1ih(_63,function(_bC,_){return new F(function(){return _5T(_63,new T(function(){return B(_1lY(_1mO[1],_1mO[2]));}),_bC,_);});},_1mP,_)),_1mT=_1mS,_1mU=B(A(_5d,[_5q,_1mT,_bP,_1lM,_])),_1mV=_1mU;return _1mP;},_lH,_19h);});};}}},_1mW=function(_1mX){var _1mY=E(_1mX);return _1mY[0]==0?E(_1lk):function(_1mZ,_){var _1n0=B(A(new T(function(){var _1n1=E(_1mY[1]);return B(_1ls(_1n1[1],_1n1[2]));}),[_1mZ,_])),_1n2=_1n0,_1n3=B(A(new T(function(){return B(_1mW(_1mY[2]));}),[_1mZ,_])),_1n4=_1n3;return _1mZ;};},_1n5=new T(function(){return B(unCStr("errormsg"));}),_1n6=function(_bC,_){return new F(function(){return _1ih(_56,_9,_bC,_);});},_1n7=[0,10006],_1n8=[1,_1n7,_9],_1n9=function(_1na){return !B(_l0(_1na,_9))?function(_lH,_19h){return new F(function(){return _1ih(_63,function(_1nb,_){var _1nc=B(_5T(_56,_1n8,_1nb,_)),_1nd=_1nc,_1ne=B(_5T(_56,_1na,_1nb,_)),_1nf=_1ne,_1ng=B(A(_5d,[_5q,_1nf,_bP,_1n5,_])),_1nh=_1ng;return _1nb;},_lH,_19h);});}:E(_1n6);},_1ni=function(_1nj){var _1nk=E(_1nj);return _1nk[0]==0?E(_1lk):function(_1nl,_){var _1nm=B(A(new T(function(){return B(_1n9(_1nk[1]));}),[_1nl,_])),_1nn=_1nm,_1no=B(A(new T(function(){return B(_1ni(_1nk[2]));}),[_1nl,_])),_1np=_1no;return _1nl;};},_1nq=[0,10],_1nr=[1,_1nq,_9],_1ns=function(_1nt,_1nu,_){var _1nv=jsCreateElem(toJSStr(E(_1nt))),_1nw=_1nv,_1nx=jsAppendChild(_1nw,E(_1nu)[1]);return [0,_1nw];},_1ny=function(_1nz,_1nA,_1nB,_){var _1nC=B(_1ns(_1nz,_1nB,_)),_1nD=_1nC,_1nE=B(A(_1nA,[_1nD,_])),_1nF=_1nE;return _1nD;},_1nG=new T(function(){return B(unCStr("()"));}),_1nH=new T(function(){return B(unCStr("GHC.Tuple"));}),_1nI=new T(function(){return B(unCStr("ghc-prim"));}),_1nJ=new T(function(){var _1nK=hs_wordToWord64(2170319554),_1nL=_1nK,_1nM=hs_wordToWord64(26914641),_1nN=_1nM;return [0,_1nL,_1nN,[0,_1nL,_1nN,_1nI,_1nH,_1nG],_9];}),_1nO=function(_1nP){return E(_1nJ);},_1nQ=new T(function(){return B(unCStr("PerchM"));}),_1nR=new T(function(){return B(unCStr("Haste.Perch"));}),_1nS=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1nT=new T(function(){var _1nU=hs_wordToWord64(3005229400),_1nV=_1nU,_1nW=hs_wordToWord64(2682402736),_1nX=_1nW;return [0,_1nV,_1nX,[0,_1nV,_1nX,_1nS,_1nR,_1nQ],_9];}),_1nY=function(_1nZ){return E(_1nT);},_1o0=function(_1o1){var _1o2=E(_1o1);if(!_1o2[0]){return [0];}else{var _1o3=E(_1o2[1]);return [1,[0,_1o3[1],_1o3[2]],new T(function(){return B(_1o0(_1o2[2]));})];}},_1o4=function(_1o5,_1o6){var _1o7=E(_1o5);if(!_1o7){return [0,_9,_1o6];}else{var _1o8=E(_1o6);if(!_1o8[0]){return [0,_9,_9];}else{var _1o9=new T(function(){var _1oa=B(_1o4(_1o7-1|0,_1o8[2]));return [0,_1oa[1],_1oa[2]];});return [0,[1,_1o8[1],new T(function(){return E(E(_1o9)[1]);})],new T(function(){return E(E(_1o9)[2]);})];}}},_1ob=[0,120],_1oc=[0,48],_1od=function(_1oe){var _1of=new T(function(){var _1og=B(_1o4(8,new T(function(){var _1oh=md5(toJSStr(E(_1oe))),_1oi=_1oh;return fromJSStr(_1oi);})));return [0,_1og[1],_1og[2]];}),_1oj=parseInt([0,toJSStr([1,_1oc,[1,_1ob,new T(function(){return E(E(_1of)[1]);})]])]),_1ok=_1oj,_1ol=new T(function(){var _1om=B(_1o4(8,new T(function(){return E(E(_1of)[2]);})));return [0,_1om[1],_1om[2]];}),_1on=parseInt([0,toJSStr([1,_1oc,[1,_1ob,new T(function(){return E(E(_1ol)[1]);})]])]),_1oo=_1on,_1op=hs_mkWord64(_1ok,_1oo),_1oq=_1op,_1or=parseInt([0,toJSStr([1,_1oc,[1,_1ob,new T(function(){return E(B(_1o4(8,new T(function(){return E(E(_1ol)[2]);})))[1]);})]])]),_1os=_1or,_1ot=hs_mkWord64(_1os,_1os),_1ou=_1ot;return [0,_1oq,_1ou];},_1ov=function(_1ow,_1ox){var _1oy=jsShowI(_1ow),_1oz=_1oy,_1oA=md5(_1oz),_1oB=_1oA;return new F(function(){return _e(fromJSStr(_1oB),new T(function(){var _1oC=jsShowI(_1ox),_1oD=_1oC,_1oE=md5(_1oD),_1oF=_1oE;return fromJSStr(_1oF);},1));});},_1oG=function(_1oH){var _1oI=E(_1oH);return new F(function(){return _1ov(_1oI[1],_1oI[2]);});},_1oJ=function(_1oK,_1oL){return function(_1oM){return E(new T(function(){var _1oN=B(A(_1oK,[_])),_1oO=E(_1oN[3]),_1oP=_1oO[1],_1oQ=_1oO[2],_1oR=B(_e(_1oN[4],[1,new T(function(){return B(A(_1oL,[_]));}),_9]));if(!_1oR[0]){var _1oS=[0,_1oP,_1oQ,_1oO,_9];}else{var _1oT=B(_1od(new T(function(){return B(_7r(B(_7X(_1oG,[1,[0,_1oP,_1oQ],new T(function(){return B(_1o0(_1oR));})]))));},1))),_1oS=[0,_1oT[1],_1oT[2],_1oO,_1oR];}var _1oU=_1oS,_1oV=_1oU;return _1oV;}));};},_1oW=new T(function(){return B(_1oJ(_1nY,_1nO));}),_1oX=function(_1oY,_1oZ,_1p0,_){var _1p1=E(_1oZ),_1p2=B(A(_1oY,[_1p0,_])),_1p3=_1p2,_1p4=B(A(_5d,[_5q,_1p3,_1p1[1],_1p1[2],_])),_1p5=_1p4;return _1p3;},_1p6=function(_1p7,_1p8){while(1){var _1p9=(function(_1pa,_1pb){var _1pc=E(_1pb);if(!_1pc[0]){return E(_1pa);}else{_1p7=function(_1pd,_){return new F(function(){return _1oX(_1pa,_1pc[1],_1pd,_);});};_1p8=_1pc[2];return null;}})(_1p7,_1p8);if(_1p9!=null){return _1p9;}}},_1pe=new T(function(){return B(unCStr("value"));}),_1pf=new T(function(){return B(unCStr("id"));}),_1pg=new T(function(){return B(unCStr("onclick"));}),_1ph=new T(function(){return B(unCStr("checked"));}),_1pi=[0,_1ph,_9],_1pj=new T(function(){return B(unCStr("type"));}),_1pk=new T(function(){return B(unCStr("input"));}),_1pl=function(_1pm,_){return new F(function(){return _1ns(_1pk,_1pm,_);});},_1pn=function(_1po,_1pp,_1pq){return new F(function(){return _1p6(function(_1pd,_){return new F(function(){return _1oX(_1po,_1pp,_1pd,_);});},_1pq);});},_1pr=function(_1ps,_1pt,_1pu,_1pv,_1pw){var _1px=new T(function(){var _1py=new T(function(){return B(_1pn(_1pl,[0,_1pj,_1pt],[1,[0,_1pf,_1ps],[1,[0,_1pe,_1pu],_9]]));});return !E(_1pv)?E(_1py):B(_1pn(_1py,_1pi,_9));}),_1pz=E(_1pw);return _1pz[0]==0?E(_1px):B(_1pn(_1px,[0,_1pg,_1pz[1]],_9));},_1pA=new T(function(){return B(unCStr("href"));}),_1pB=[0,97],_1pC=[1,_1pB,_9],_1pD=function(_1pE,_){return new F(function(){return _1ns(_1pC,_1pE,_);});},_1pF=function(_1pG,_1pH){return function(_1pI,_){var _1pJ=B(A(new T(function(){return B(_1pn(_1pD,[0,_1pA,_1pG],_9));}),[_1pI,_])),_1pK=_1pJ,_1pL=B(A(_1pH,[_1pK,_])),_1pM=_1pL;return _1pK;};},_1pN=function(_1pO){return new F(function(){return _1pF(_1pO,function(_1pd,_){return new F(function(){return _56(_1pO,_1pd,_);});});});},_1pP=new T(function(){return B(unCStr("option"));}),_1pQ=function(_1pR,_){return new F(function(){return _1ns(_1pP,_1pR,_);});},_1pS=new T(function(){return B(unCStr("selected"));}),_1pT=[0,_1pS,_9],_1pU=function(_1pV,_1pW,_1pX){var _1pY=new T(function(){return B(_1pn(_1pQ,[0,_1pe,_1pV],_9));});if(!E(_1pX)){return function(_1pZ,_){var _1q0=B(A(_1pY,[_1pZ,_])),_1q1=_1q0,_1q2=B(A(_1pW,[_1q1,_])),_1q3=_1q2;return _1q1;};}else{return new F(function(){return _1pn(function(_1q4,_){var _1q5=B(A(_1pY,[_1q4,_])),_1q6=_1q5,_1q7=B(A(_1pW,[_1q6,_])),_1q8=_1q7;return _1q6;},_1pT,_9);});}},_1q9=function(_1qa,_1qb){return new F(function(){return _1pU(_1qa,function(_1pd,_){return new F(function(){return _56(_1qa,_1pd,_);});},_1qb);});},_1qc=new T(function(){return B(unCStr("method"));}),_1qd=new T(function(){return B(unCStr("action"));}),_1qe=new T(function(){return B(unCStr("UTF-8"));}),_1qf=new T(function(){return B(unCStr("acceptCharset"));}),_1qg=[0,_1qf,_1qe],_1qh=new T(function(){return B(unCStr("form"));}),_1qi=function(_1qj,_){return new F(function(){return _1ns(_1qh,_1qj,_);});},_1qk=function(_1ql,_1qm,_1qn){return function(_1qo,_){var _1qp=B(A(new T(function(){return B(_1pn(_1qi,_1qg,[1,[0,_1qd,_1ql],[1,[0,_1qc,_1qm],_9]]));}),[_1qo,_])),_1qq=_1qp,_1qr=B(A(_1qn,[_1qq,_])),_1qs=_1qr;return _1qq;};},_1qt=new T(function(){return B(unCStr("select"));}),_1qu=function(_1qv,_){return new F(function(){return _1ns(_1qt,_1qv,_);});},_1qw=function(_1qx,_1qy){return function(_1qz,_){var _1qA=B(A(new T(function(){return B(_1pn(_1qu,[0,_1pf,_1qx],_9));}),[_1qz,_])),_1qB=_1qA,_1qC=B(A(_1qy,[_1qB,_])),_1qD=_1qC;return _1qB;};},_1qE=new T(function(){return B(unCStr("textarea"));}),_1qF=function(_1qG,_){return new F(function(){return _1ns(_1qE,_1qG,_);});},_1qH=function(_1qI,_1qJ){return function(_1qK,_){var _1qL=B(A(new T(function(){return B(_1pn(_1qF,[0,_1pf,_1qI],_9));}),[_1qK,_])),_1qM=_1qL,_1qN=B(_56(_1qJ,_1qM,_)),_1qO=_1qN;return _1qM;};},_1qP=new T(function(){return B(unCStr("color:red"));}),_1qQ=new T(function(){return B(unCStr("style"));}),_1qR=[0,_1qQ,_1qP],_1qS=[0,98],_1qT=[1,_1qS,_9],_1qU=function(_1qV){return new F(function(){return _1pn(function(_1qW,_){var _1qX=B(_1ns(_1qT,_1qW,_)),_1qY=_1qX,_1qZ=B(A(_1qV,[_1qY,_])),_1r0=_1qZ;return _1qY;},_1qR,_9);});},_1r1=function(_1r2,_1r3,_){var _1r4=E(_1r2);if(!_1r4[0]){return _1r3;}else{var _1r5=B(A(_1r4[1],[_1r3,_])),_1r6=_1r5,_1r7=B(_1r1(_1r4[2],_1r3,_)),_1r8=_1r7;return _1r3;}},_1r9=function(_1ra,_1rb,_){return new F(function(){return _1r1(_1ra,_1rb,_);});},_1rc=function(_1rd,_1re,_1rf,_){var _1rg=B(A(_1rd,[_1rf,_])),_1rh=_1rg,_1ri=B(A(_1re,[_1rf,_])),_1rj=_1ri;return _1rf;},_1rk=[0,_5t,_1rc,_1r9],_1rl=[0,_1rk,_1oW,_56,_56,_1ny,_1qU,_1pF,_1pN,_1pr,_1qH,_1qw,_1pU,_1q9,_1qk,_1p6],_1rm=function(_1rn,_1ro,_){var _1rp=B(A(_1ro,[_])),_1rq=_1rp;return _1rn;},_1rr=function(_1rs,_1rt,_){var _1ru=B(A(_1rt,[_])),_1rv=_1ru;return new T(function(){return B(A(_1rs,[_1rv]));});},_1rw=[0,_1rr,_1rm],_1rx=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1ry=new T(function(){return B(unCStr("base"));}),_1rz=new T(function(){return B(unCStr("IOException"));}),_1rA=new T(function(){var _1rB=hs_wordToWord64(4053623282),_1rC=_1rB,_1rD=hs_wordToWord64(3693590983),_1rE=_1rD;return [0,_1rC,_1rE,[0,_1rC,_1rE,_1ry,_1rx,_1rz],_9];}),_1rF=function(_1rG){return E(_1rA);},_1rH=function(_1rI){var _1rJ=E(_1rI);return new F(function(){return _2y(B(_2w(_1rJ[1])),_1rF,_1rJ[2]);});},_1rK=new T(function(){return B(unCStr(": "));}),_1rL=[0,41],_1rM=new T(function(){return B(unCStr(" ("));}),_1rN=new T(function(){return B(unCStr("already exists"));}),_1rO=new T(function(){return B(unCStr("does not exist"));}),_1rP=new T(function(){return B(unCStr("protocol error"));}),_1rQ=new T(function(){return B(unCStr("failed"));}),_1rR=new T(function(){return B(unCStr("invalid argument"));}),_1rS=new T(function(){return B(unCStr("inappropriate type"));}),_1rT=new T(function(){return B(unCStr("hardware fault"));}),_1rU=new T(function(){return B(unCStr("unsupported operation"));}),_1rV=new T(function(){return B(unCStr("timeout"));}),_1rW=new T(function(){return B(unCStr("resource vanished"));}),_1rX=new T(function(){return B(unCStr("interrupted"));}),_1rY=new T(function(){return B(unCStr("resource busy"));}),_1rZ=new T(function(){return B(unCStr("resource exhausted"));}),_1s0=new T(function(){return B(unCStr("end of file"));}),_1s1=new T(function(){return B(unCStr("illegal operation"));}),_1s2=new T(function(){return B(unCStr("permission denied"));}),_1s3=new T(function(){return B(unCStr("user error"));}),_1s4=new T(function(){return B(unCStr("unsatisified constraints"));}),_1s5=new T(function(){return B(unCStr("system error"));}),_1s6=function(_1s7,_1s8){switch(E(_1s7)){case 0:return new F(function(){return _e(_1rN,_1s8);});break;case 1:return new F(function(){return _e(_1rO,_1s8);});break;case 2:return new F(function(){return _e(_1rY,_1s8);});break;case 3:return new F(function(){return _e(_1rZ,_1s8);});break;case 4:return new F(function(){return _e(_1s0,_1s8);});break;case 5:return new F(function(){return _e(_1s1,_1s8);});break;case 6:return new F(function(){return _e(_1s2,_1s8);});break;case 7:return new F(function(){return _e(_1s3,_1s8);});break;case 8:return new F(function(){return _e(_1s4,_1s8);});break;case 9:return new F(function(){return _e(_1s5,_1s8);});break;case 10:return new F(function(){return _e(_1rP,_1s8);});break;case 11:return new F(function(){return _e(_1rQ,_1s8);});break;case 12:return new F(function(){return _e(_1rR,_1s8);});break;case 13:return new F(function(){return _e(_1rS,_1s8);});break;case 14:return new F(function(){return _e(_1rT,_1s8);});break;case 15:return new F(function(){return _e(_1rU,_1s8);});break;case 16:return new F(function(){return _e(_1rV,_1s8);});break;case 17:return new F(function(){return _e(_1rW,_1s8);});break;default:return new F(function(){return _e(_1rX,_1s8);});}},_1s9=[0,125],_1sa=new T(function(){return B(unCStr("{handle: "));}),_1sb=function(_1sc,_1sd,_1se,_1sf,_1sg,_1sh){var _1si=new T(function(){var _1sj=new T(function(){return B(_1s6(_1sd,new T(function(){var _1sk=E(_1sf);return _1sk[0]==0?E(_1sh):B(_e(_1rM,new T(function(){return B(_e(_1sk,[1,_1rL,_1sh]));},1)));},1)));},1),_1sl=E(_1se);return _1sl[0]==0?E(_1sj):B(_e(_1sl,new T(function(){return B(_e(_1rK,_1sj));},1)));},1),_1sm=E(_1sg);if(!_1sm[0]){var _1sn=E(_1sc);if(!_1sn[0]){return E(_1si);}else{var _1so=E(_1sn[1]);return _1so[0]==0?B(_e(_1sa,new T(function(){return B(_e(_1so[1],[1,_1s9,new T(function(){return B(_e(_1rK,_1si));})]));},1))):B(_e(_1sa,new T(function(){return B(_e(_1so[1],[1,_1s9,new T(function(){return B(_e(_1rK,_1si));})]));},1)));}}else{return new F(function(){return _e(_1sm[1],new T(function(){return B(_e(_1rK,_1si));},1));});}},_1sp=function(_1sq){var _1sr=E(_1sq);return new F(function(){return _1sb(_1sr[1],_1sr[2],_1sr[3],_1sr[4],_1sr[6],_9);});},_1ss=function(_1st,_1su){var _1sv=E(_1st);return new F(function(){return _1sb(_1sv[1],_1sv[2],_1sv[3],_1sv[4],_1sv[6],_1su);});},_1sw=function(_1sx,_1sy){return new F(function(){return _2T(_1ss,_1sx,_1sy);});},_1sz=function(_1sA,_1sB,_1sC){var _1sD=E(_1sB);return new F(function(){return _1sb(_1sD[1],_1sD[2],_1sD[3],_1sD[4],_1sD[6],_1sC);});},_1sE=[0,_1sz,_1sp,_1sw],_1sF=new T(function(){return [0,_1rF,_1sE,_1sG,_1rH];}),_1sG=function(_1sH){return [0,_1sF,_1sH];},_1sI=7,_1sJ=function(_1sK){return [0,_28,_1sI,_9,_1sK,_28,_28];},_1sL=function(_1sM,_){return new F(function(){return die(new T(function(){return B(_1sG(new T(function(){return B(_1sJ(_1sM));})));}));});},_1sN=function(_1sO,_){return new F(function(){return _1sL(_1sO,_);});},_1sP=function(_1sQ,_){return new F(function(){return _1sN(_1sQ,_);});},_1sR=function(_1sS,_){return new F(function(){return _1sP(_1sS,_);});},_1sT=function(_1sU,_1sV,_){var _1sW=B(A(_1sU,[_])),_1sX=_1sW;return new F(function(){return A(_1sV,[_1sX,_]);});},_1sY=function(_1sZ,_1t0,_){var _1t1=B(A(_1sZ,[_])),_1t2=_1t1;return new F(function(){return A(_1t0,[_]);});},_1t3=[0,_1sT,_1sY,_5t,_1sR],_1t4=[0,_1t3,_5q],_1t5=function(_1t6){return E(E(_1t6)[1]);},_1t7=function(_1t8){return E(E(_1t8)[2]);},_1t9=function(_1ta,_1tb){var _1tc=new T(function(){return B(_1t5(_1ta));});return function(_1td){return new F(function(){return A(new T(function(){return B(_Nl(_1tc));}),[new T(function(){return B(A(_1t7,[_1ta,_1tb]));}),function(_1te){return new F(function(){return A(new T(function(){return B(_ir(_1tc));}),[[0,_1te,_1td]]);});}]);});};},_1tf=function(_1tg,_1th){return [0,_1tg,function(_1ti){return new F(function(){return _1t9(_1th,_1ti);});}];},_1tj=function(_1tk,_1tl,_1tm,_1tn){return new F(function(){return A(_Nl,[_1tk,new T(function(){return B(A(_1tl,[_1tn]));}),function(_1to){return new F(function(){return A(_1tm,[new T(function(){return E(E(_1to)[1]);}),new T(function(){return E(E(_1to)[2]);})]);});}]);});},_1tp=function(_1tq,_1tr,_1ts,_1tt){return new F(function(){return A(_Nl,[_1tq,new T(function(){return B(A(_1tr,[_1tt]));}),function(_1tu){return new F(function(){return A(_1ts,[new T(function(){return E(E(_1tu)[2]);})]);});}]);});},_1tv=function(_1tw,_1tx,_1ty,_1tz){return new F(function(){return _1tp(_1tw,_1tx,_1ty,_1tz);});},_1tA=function(_1tB){return E(E(_1tB)[4]);},_1tC=function(_1tD,_1tE){return function(_1tF){return E(new T(function(){return B(A(_1tA,[_1tD,_1tE]));}));};},_1tG=function(_1tH){return [0,function(_1tx,_1ty,_1tz){return new F(function(){return _1tj(_1tH,_1tx,_1ty,_1tz);});},function(_1tx,_1ty,_1tz){return new F(function(){return _1tv(_1tH,_1tx,_1ty,_1tz);});},function(_1tI,_1tJ){return new F(function(){return A(new T(function(){return B(_ir(_1tH));}),[[0,_1tI,_1tJ]]);});},function(_1tz){return new F(function(){return _1tC(_1tH,_1tz);});}];},_1tK=function(_1tL,_1tM,_1tN){return new F(function(){return A(_ir,[_1tL,[0,_1tM,_1tN]]);});},_1tO=[0,10],_1tP=function(_1tQ,_1tR){var _1tS=E(_1tR);if(!_1tS[0]){return E(_5q);}else{var _1tT=_1tS[1],_1tU=E(_1tS[2]);if(!_1tU[0]){var _1tV=E(_1tT);return new F(function(){return _1tW(_1tO,_1tV[3],_1tV[4]);});}else{return function(_1tX){return new F(function(){return A(new T(function(){var _1tY=E(_1tT);return B(_1tW(_1tO,_1tY[3],_1tY[4]));}),[new T(function(){return B(A(_1tQ,[new T(function(){return B(A(new T(function(){return B(_1tP(_1tQ,_1tU));}),[_1tX]));})]));})]);});};}}},_1tZ=new T(function(){return B(unCStr("(->)"));}),_1u0=new T(function(){return B(unCStr("GHC.Prim"));}),_1u1=new T(function(){var _1u2=hs_wordToWord64(4173248105),_1u3=_1u2,_1u4=hs_wordToWord64(4270398258),_1u5=_1u4;return [0,_1u3,_1u5,[0,_1u3,_1u5,_1nI,_1u0,_1tZ],_9];}),_1u6=new T(function(){return E(E(_1u1)[3]);}),_1u7=new T(function(){return B(unCStr("GHC.Types"));}),_1u8=new T(function(){return B(unCStr("[]"));}),_1u9=new T(function(){var _1ua=hs_wordToWord64(4033920485),_1ub=_1ua,_1uc=hs_wordToWord64(786266835),_1ud=_1uc;return [0,_1ub,_1ud,[0,_1ub,_1ud,_1nI,_1u7,_1u8],_9];}),_1ue=[1,_1nJ,_9],_1uf=function(_1ug){var _1uh=E(_1ug);if(!_1uh[0]){return [0];}else{var _1ui=E(_1uh[1]);return [1,[0,_1ui[1],_1ui[2]],new T(function(){return B(_1uf(_1uh[2]));})];}},_1uj=new T(function(){var _1uk=E(_1u9),_1ul=E(_1uk[3]),_1um=B(_e(_1uk[4],_1ue));if(!_1um[0]){var _1un=E(_1ul);}else{var _1uo=B(_1od(new T(function(){return B(_7r(B(_7X(_1oG,[1,[0,_1ul[1],_1ul[2]],new T(function(){return B(_1uf(_1um));})]))));},1))),_1un=E(_1ul);}var _1up=_1un,_1uq=_1up;return _1uq;}),_1ur=[0,8],_1us=[0,32],_1ut=function(_1uu){return [1,_1us,_1uu];},_1uv=new T(function(){return B(unCStr(" -> "));}),_1uw=[0,9],_1ux=[0,93],_1uy=[0,91],_1uz=[0,41],_1uA=[0,44],_1uB=function(_1uu){return [1,_1uA,_1uu];},_1uC=[0,40],_1uD=[0,0],_1tW=function(_1uE,_1uF,_1uG){var _1uH=E(_1uG);if(!_1uH[0]){return function(_1uI){return new F(function(){return _e(E(_1uF)[5],_1uI);});};}else{var _1uJ=_1uH[1],_1uK=function(_1uL){var _1uM=E(_1uF)[5],_1uN=function(_1uO){var _1uP=new T(function(){return B(_1tP(_1ut,_1uH));});return E(_1uE)[1]<=9?function(_1uQ){return new F(function(){return _e(_1uM,[1,_1us,new T(function(){return B(A(_1uP,[_1uQ]));})]);});}:function(_1uR){return [1,_E,new T(function(){return B(_e(_1uM,[1,_1us,new T(function(){return B(A(_1uP,[[1,_D,_1uR]]));})]));})];};},_1uS=E(_1uM);if(!_1uS[0]){return new F(function(){return _1uN(_);});}else{if(E(E(_1uS[1])[1])==40){var _1uT=E(_1uS[2]);if(!_1uT[0]){return new F(function(){return _1uN(_);});}else{if(E(E(_1uT[1])[1])==44){return function(_1uU){return [1,_1uC,new T(function(){return B(A(new T(function(){return B(_1tP(_1uB,_1uH));}),[[1,_1uz,_1uU]]));})];};}else{return new F(function(){return _1uN(_);});}}}else{return new F(function(){return _1uN(_);});}}},_1uV=E(_1uH[2]);if(!_1uV[0]){var _1uW=E(_1uF),_1uX=E(_1uj),_1uY=hs_eqWord64(_1uW[1],_1uX[1]),_1uZ=_1uY;if(!E(_1uZ)){return new F(function(){return _1uK(_);});}else{var _1v0=hs_eqWord64(_1uW[2],_1uX[2]),_1v1=_1v0;if(!E(_1v1)){return new F(function(){return _1uK(_);});}else{return function(_1v2){return [1,_1uy,new T(function(){return B(A(new T(function(){var _1v3=E(_1uJ);return B(_1tW(_1uD,_1v3[3],_1v3[4]));}),[[1,_1ux,_1v2]]));})];};}}}else{if(!E(_1uV[2])[0]){var _1v4=E(_1uF),_1v5=E(_1u6),_1v6=hs_eqWord64(_1v4[1],_1v5[1]),_1v7=_1v6;if(!E(_1v7)){return new F(function(){return _1uK(_);});}else{var _1v8=hs_eqWord64(_1v4[2],_1v5[2]),_1v9=_1v8;if(!E(_1v9)){return new F(function(){return _1uK(_);});}else{var _1va=new T(function(){var _1vb=E(_1uV[1]);return B(_1tW(_1ur,_1vb[3],_1vb[4]));}),_1vc=new T(function(){var _1vd=E(_1uJ);return B(_1tW(_1uw,_1vd[3],_1vd[4]));});return E(_1uE)[1]<=8?function(_1ve){return new F(function(){return A(_1vc,[new T(function(){return B(_e(_1uv,new T(function(){return B(A(_1va,[_1ve]));},1)));})]);});}:function(_1vf){return [1,_E,new T(function(){return B(A(_1vc,[new T(function(){return B(_e(_1uv,new T(function(){return B(A(_1va,[[1,_D,_1vf]]));},1)));})]));})];};}}}else{return new F(function(){return _1uK(_);});}}}},_1vg=function(_1vh,_1vi){return new F(function(){return A(_1vh,[function(_){return new F(function(){return jsFind(toJSStr(E(_1vi)));});}]);});},_1vj=[0],_1vk=function(_1vl){return E(E(_1vl)[3]);},_1vm=new T(function(){return [0,"value"];}),_1vn=function(_1vo){return E(E(_1vo)[6]);},_1vp=function(_1vq){return E(E(_1vq)[1]);},_1vr=new T(function(){return B(unCStr("Char"));}),_1vs=new T(function(){var _1vt=hs_wordToWord64(3763641161),_1vu=_1vt,_1vv=hs_wordToWord64(1343745632),_1vw=_1vv;return [0,_1vu,_1vw,[0,_1vu,_1vw,_1nI,_1u7,_1vr],_9];}),_1vx=function(_1vy){return E(_1vs);},_1vz=function(_1vA){return E(_1u9);},_1vB=new T(function(){return B(_1oJ(_1vz,_1vx));}),_1vC=new T(function(){return B(A(_1vB,[_]));}),_1vD=function(_1vE,_1vF,_1vG,_1vH,_1vI,_1vJ,_1vK,_1vL,_1vM){var _1vN=new T(function(){return B(A(_1vH,[_1vj]));});return new F(function(){return A(_1vF,[new T(function(){return B(_1vg(E(_1vE)[2],_1vM));}),function(_1vO){var _1vP=E(_1vO);return _1vP[0]==0?E(_1vN):B(A(_1vF,[new T(function(){return B(A(E(_1vE)[2],[function(_){var _1vQ=jsGet(E(_1vP[1])[1],E(_1vm)[1]),_1vR=_1vQ;return [1,new T(function(){return fromJSStr(_1vR);})];}]));}),function(_1vS){var _1vT=E(_1vS);if(!_1vT[0]){return E(_1vN);}else{var _1vU=_1vT[1];if(!E(new T(function(){var _1vV=B(A(_1vJ,[_])),_1vW=E(_1vC),_1vX=hs_eqWord64(_1vV[1],_1vW[1]),_1vY=_1vX;if(!E(_1vY)){var _1vZ=false;}else{var _1w0=hs_eqWord64(_1vV[2],_1vW[2]),_1w1=_1w0,_1vZ=E(_1w1)==0?false:true;}var _1w2=_1vZ,_1w3=_1w2;return _1w3;}))){var _1w4=function(_1w5){return new F(function(){return A(_1vH,[[1,_1vU,new T(function(){return B(A(new T(function(){return B(_1vn(_1vL));}),[new T(function(){return B(A(new T(function(){return B(_1vk(_1vL));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_e(_1vU,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1w6=B(A(_1vJ,[_]));return B(A(_1tW,[_1uD,_1w6[3],_1w6[4],_9]));})));})));})));})]));})]));})]]);});},_1w7=B(A(new T(function(){return B(A(_1vp,[_1vK,_1R]));}),[_1vU]));if(!_1w7[0]){return new F(function(){return _1w4(_);});}else{var _1w8=E(_1w7[1]);return E(_1w8[2])[0]==0?E(_1w7[2])[0]==0?B(A(_1vH,[[2,_1w8[1]]])):B(_1w4(_)):B(_1w4(_));}}else{return new F(function(){return A(_1vH,[[2,_1vU]]);});}}}]));}]);});},_1w9=function(_1wa){return E(E(_1wa)[10]);},_1wb=function(_1wc){return new F(function(){return _kt([1,function(_1wd){return new F(function(){return A(_s9,[_1wd,function(_1we){return E(new T(function(){return B(_tp(function(_1wf){var _1wg=E(_1wf);return _1wg[0]==0?B(A(_1wc,[_1wg[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_tL(_1wh,_1wc))];}));});},_1wh=function(_1wi,_1wj){return new F(function(){return _1wb(_1wj);});},_1wk=[0,91],_1wl=[1,_1wk,_9],_1wm=function(_1wn,_1wo){var _1wp=function(_1wq,_1wr){return [1,function(_1ws){return new F(function(){return A(_s9,[_1ws,function(_1wt){return E(new T(function(){return B(_tp(function(_1wu){var _1wv=E(_1wu);if(_1wv[0]==2){var _1ww=E(_1wv[1]);if(!_1ww[0]){return [2];}else{var _1wx=_1ww[2];switch(E(E(_1ww[1])[1])){case 44:return E(_1wx)[0]==0?!E(_1wq)?[2]:E(new T(function(){return B(A(_1wn,[_tK,function(_1wy){return new F(function(){return _1wp(_nG,function(_1wz){return new F(function(){return A(_1wr,[[1,_1wy,_1wz]]);});});});}]));})):[2];case 93:return E(_1wx)[0]==0?E(new T(function(){return B(A(_1wr,[_9]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1wA=function(_1wB){return new F(function(){return _kt([1,function(_1wC){return new F(function(){return A(_s9,[_1wC,function(_1wD){return E(new T(function(){return B(_tp(function(_1wE){var _1wF=E(_1wE);return _1wF[0]==2?!B(_l0(_1wF[1],_1wl))?[2]:E(new T(function(){return B(_kt(B(_1wp(_1S,_1wB)),new T(function(){return B(A(_1wn,[_tK,function(_1wG){return new F(function(){return _1wp(_nG,function(_1wH){return new F(function(){return A(_1wB,[[1,_1wG,_1wH]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_tL(function(_1wI,_1wJ){return new F(function(){return _1wA(_1wJ);});},_1wB))];}));});};return new F(function(){return _1wA(_1wo);});},_1wK=function(_1wL){return new F(function(){return _kt(B(_kt([1,function(_1wM){return new F(function(){return A(_s9,[_1wM,function(_1wN){return E(new T(function(){return B(_tp(function(_1wO){var _1wP=E(_1wO);return _1wP[0]==1?B(A(_1wL,[_1wP[1]])):[2];}));}));}]);});}],new T(function(){return B(_1wm(_1wh,_1wL));}))),new T(function(){return [1,B(_tL(_1wQ,_1wL))];}));});},_1wQ=function(_1wR,_1wS){return new F(function(){return _1wK(_1wS);});},_1wT=new T(function(){return B(_1wK(_lh));}),_1wU=function(_1wV){return new F(function(){return _kj(_1wT,_1wV);});},_1wW=new T(function(){return B(_1wb(_lh));}),_1wX=function(_1wV){return new F(function(){return _kj(_1wW,_1wV);});},_1wY=function(_1wZ){return E(_1wX);},_1x0=[0,_1wY,_1wU,_1wh,_1wQ],_1x1=function(_1x2){return E(E(_1x2)[4]);},_1x3=function(_1x4,_1x5,_1x6){return new F(function(){return _1wm(new T(function(){return B(_1x1(_1x4));}),_1x6);});},_1x7=function(_1x8){return function(_lH){return new F(function(){return _kj(new T(function(){return B(_1wm(new T(function(){return B(_1x1(_1x8));}),_lh));}),_lH);});};},_1x9=function(_1xa,_1xb){return function(_lH){return new F(function(){return _kj(new T(function(){return B(A(_1x1,[_1xa,_1xb,_lh]));}),_lH);});};},_1xc=function(_1xd){return [0,function(_1wV){return new F(function(){return _1x9(_1xd,_1wV);});},new T(function(){return B(_1x7(_1xd));}),new T(function(){return B(_1x1(_1xd));}),function(_1xe,_1wV){return new F(function(){return _1x3(_1xd,_1xe,_1wV);});}];},_1xf=new T(function(){return B(_1xc(_1x0));}),_1xg=function(_1xh,_1xi,_1xj){var _1xk=new T(function(){return B(_1w9(_1xh));}),_1xl=new T(function(){return B(_1t5(_1xj));}),_1xm=new T(function(){return B(_ir(_1xl));});return function(_1xn,_1xo){return new F(function(){return A(new T(function(){return B(_Nl(_1xl));}),[new T(function(){return B(A(new T(function(){return B(_Nl(_1xl));}),[new T(function(){return B(A(new T(function(){return B(_ir(_1xl));}),[[0,_1xo,_1xo]]));}),function(_1xp){var _1xq=new T(function(){return E(E(_1xp)[1]);}),_1xr=new T(function(){return E(E(_1xq)[2]);});return new F(function(){return A(new T(function(){return B(_Nl(_1xl));}),[new T(function(){return B(A(new T(function(){return B(_ir(_1xl));}),[[0,_5c,new T(function(){var _1xs=E(_1xq);return [0,_1xs[1],new T(function(){return [0,E(_1xr)[1]+1|0];}),_1xs[3],_1xs[4],_1xs[5],_1xs[6],_1xs[7]];})]]));}),function(_1xt){return new F(function(){return A(new T(function(){return B(_ir(_1xl));}),[[0,[1,_5j,new T(function(){return B(_e(B(_F(0,E(_1xr)[1],_9)),new T(function(){return E(E(_1xq)[1]);},1)));})],new T(function(){return E(E(_1xt)[2]);})]]);});}]);});}]));}),function(_1xu){var _1xv=new T(function(){return E(E(_1xu)[1]);});return new F(function(){return A(new T(function(){return B(_Nl(_1xl));}),[new T(function(){return B(A(_1vD,[new T(function(){return B(_1tf(new T(function(){return B(_1tG(_1xl));}),_1xj));}),function(_1xw,_1pd,_1xx){return new F(function(){return _1tj(_1xl,_1xw,_1pd,_1xx);});},function(_1xw,_1pd,_1xx){return new F(function(){return _1tv(_1xl,_1xw,_1pd,_1xx);});},function(_1pd,_1xx){return new F(function(){return _1tK(_1xl,_1pd,_1xx);});},function(_1xx){return new F(function(){return _1tC(_1xl,_1xx);});},_1vB,_1xf,_1xh,_1xv,new T(function(){return E(E(_1xu)[2]);})]));}),function(_1xy){var _1xz=E(_1xy),_1xA=_1xz[2],_1xB=E(_1xz[1]);switch(_1xB[0]){case 0:return new F(function(){return A(_1xm,[[0,[0,new T(function(){return B(A(_1xk,[_1xv,_1xn]));}),_28],_1xA]]);});break;case 1:return new F(function(){return A(_1xm,[[0,[0,new T(function(){return B(A(_1xk,[_1xv,_1xB[1]]));}),_28],_1xA]]);});break;default:var _1xC=_1xB[1];return new F(function(){return A(_1xm,[[0,[0,new T(function(){return B(A(_1xk,[_1xv,_1xC]));}),[1,_1xC]],_1xA]]);});}}]);});}]);});};},_1xD=new T(function(){return B(_1xg(_1rl,_1rw,_1t4));}),_1xE=new T(function(){return B(_BP("w_s8cc{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv a7Mz} [tv]"));}),_1xF=new T(function(){return B(_BP("w_s8cd{v} [lid] main:Carnap.Core.Data.AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv a7My} [tv]"));}),_1xG=function(_1xH){return E(E(_1xH)[2]);},_1xI=function(_1xJ){return E(E(_1xJ)[1]);},_1xK=function(_1xL,_1xM,_1xN){return function(_1xO,_){var _1xP=B(A(_1xM,[_1xO,_])),_1xQ=_1xP,_1xR=E(_1xQ),_1xS=E(_1xR[1]),_1xT=new T(function(){return B(A(new T(function(){return B(_1xG(_1xL));}),[_1xN,function(_){var _1xU=E(E(_1xO)[4]),_1xV=B(A(_1xU[1],[_])),_1xW=_1xV,_1xX=E(_1xW);if(!_1xX[0]){return _5c;}else{var _1xY=B(A(_1xU[2],[_1xX[1],_])),_1xZ=_1xY;return _5c;}}]));});return [0,[0,function(_1y0,_){var _1y1=B(A(_1xS[1],[_1y0,_])),_1y2=_1y1,_1y3=E(_1y2),_1y4=E(_1xT),_1y5=jsSetCB(_1y3[1],toJSStr(E(new T(function(){return B(A(_1xI,[_1xL,_1xN]));}))),_1xT),_1y6=_1y5;return _1y3;},_1xS[2]],_1xR[2]];};},_1y7=function(_1y8,_1y9,_1ya,_1yb,_1yc,_1yd,_1ye,_1yf,_1yg,_1yh,_1yi){return function(_1yj,_1yk){return function(_lH,_19h){return new F(function(){return _65(function(_1yl,_){var _1ym=B(A(new T(function(){return B(_1xK(_55,new T(function(){return B(_1xK(_55,new T(function(){return B(A(_1xD,[_1yk]));}),_1p));}),_1o));}),[_1yl,_])),_1yn=_1ym,_1yo=E(_1yn),_1yp=E(_1yo[1]);return [0,[0,function(_1yq,_){var _1yr=B(A(_1yp[1],[_1yq,_])),_1ys=_1yr,_1yt=B(A(_5d,[_5q,_1ys,_bP,_bu,_])),_1yu=_1yt;return _1ys;},_1yp[2]],_1yo[2]];},function(_1yv){var _1yw=new T(function(){var _1yx=B(_CX(_BT,_Dj,[0,new T(function(){return B(_e(_1yv,_1nr));}),E(_BM),E(_5c)]));if(!_1yx[0]){var _1yy=E(_1yx[1]);if(!_1yy[0]){var _1yz=E(E(_1yy[1])[1]);}else{var _1yz=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_1yy[1]));})));})],_9],_9];}var _1yA=_1yz;}else{var _1yB=E(_1yx[1]);if(!_1yB[0]){var _1yC=E(E(_1yB[1])[1]);}else{var _1yC=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9W(_1yB[1]));})));})],_9],_9];}var _1yA=_1yC;}return _1yA;});return function(_lH,_19h){return new F(function(){return _65(_bB,function(_1yD,_1yE,_){return new F(function(){return _65(_bH,function(_1yF,_1yG,_){return new F(function(){return _65(_bM,function(_1yH,_1yI,_){return new F(function(){return _65(function(_1yJ,_){return [0,[0,function(_1yK,_){var _1yL=B(_1ih(_56,_9,_1yK,_)),_1yM=_1yL,_1yN=B(A(_5d,[_5q,_1yM,_5p,_1yD,_])),_1yO=_1yN,_1yP=B(A(_5d,[_5q,_1yM,_bP,_bN,_])),_1yQ=_1yP;return _1yM;},_bT],_1yJ];},function(_1yR,_1yS,_){return new F(function(){return _65(function(_1yT,_){return [0,[0,function(_1yU,_){var _1yV=B(_5T(_63,new T(function(){return B(_1mW(_1yw));}),_1yU,_)),_1yW=_1yV,_1yX=B(A(_5d,[_5q,_1yW,_5p,_1yF,_])),_1yY=_1yX,_1yZ=B(A(_5d,[_5q,_1yW,_bP,_bO,_])),_1z0=_1yZ;return _1yW;},_bT],_1yT];},function(_1z1){return E(new T(function(){var _1z2=E(new T(function(){var _1z3=B(_1l9(_1yw,new T(function(){return E(E(_1yj)[1]);})));return _1z3[0]==0?[0,_1z3[1]]:[1,new T(function(){return B(_1hZ(_1y8,_1y9,_1ya,_1yb,_1yc,_1yd,_1ye,_1yf,_1yg,_1xE,_1xF,_1yh,_1yi,new T(function(){return E(E(_1yj)[2]);}),_1z3[1]));})];}));if(!_1z2[0]){var _1z4=function(_1z5,_){return [0,[0,function(_1z6,_){var _1z7=B(_1ih(_63,new T(function(){return B(_1ni(B(_cS(_1z2[1],_9))));}),_1z6,_)),_1z8=_1z7,_1z9=B(A(_5d,[_5q,_1z8,_5p,_1yH,_])),_1za=_1z9,_1zb=B(A(_5d,[_5q,_1z8,_bP,_bQ,_])),_1zc=_1zb;return _1z8;},_bT],_1z5];};}else{var _1zd=E(_1z2[1]);if(!_1zd[0]){var _1ze=function(_bC,_){return new F(function(){return _bY(_1yD,_bt,_bV,_bC,_);});};}else{var _1ze=function(_lH,_19h){return new F(function(){return _bY(_1yD,_bt,function(_1zf,_){return [0,[0,function(_bC,_){return new F(function(){return _5T(_56,new T(function(){var _1zg=E(_1zd[1]);return B(_bo(new T(function(){return B(_b9(_1ye,_1yd,_1yc,_1yb,_1ya,_1y8,_1y9));}),_1zg[1],_1zg[2]));}),_bC,_);});},_bT],_1zf];},_lH,_19h);});};}var _1z4=_1ze;}return _1z4;}));},_1yS,_);});},_1yI,_);});},_1yG,_);});},_1yE,_);});},_lH,_19h);});};},_lH,_19h);});};};},_1zh=function(_1zi,_1zj,_1zk,_1zl){return new F(function(){return A(_1zi,[function(_){var _1zm=jsSet(E(_1zj)[1],toJSStr(E(_1zk)),toJSStr(E(_1zl)));return _5c;}]);});},_1zn=new T(function(){return B(unCStr("innerHTML"));}),_1zo=new T(function(){return B(unCStr("textContent"));}),_1zp=function(_1zq,_1zr,_1zs,_1zt,_1zu,_1zv,_1zw,_1zx,_1zy,_1zz,_1zA,_1zB,_1zC,_){var _1zD=B(_1j(_1zC,_1zo,_)),_1zE=_1zD,_1zF=[0,_1zC],_1zG=B(A(_1zh,[_5q,_1zF,_1zn,_9,_])),_1zH=_1zG,_1zI=E(_2l)[1],_1zJ=takeMVar(_1zI),_1zK=_1zJ,_1zL=B(A(_1y7,[_1zq,_1zr,_1zs,_1zt,_1zu,_1zv,_1zw,_1zx,_1zy,_1zz,_1zA,_1zB,_1zE,_1zK,_])),_1zM=_1zL,_1zN=E(_1zM),_1zO=E(_1zN[1]),_=putMVar(_1zI,_1zN[2]),_1zP=B(A(_1zO[1],[_1zF,_])),_1zQ=_1zP;return _1zO[2];},_1zR=function(_){var _1zS=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_1zT=_1zS;return _5c;},_1zU=new T(function(){return B(unCStr("embedding complete"));}),_1zV=new T(function(){return B(unCStr("proofbox"));}),_1zW=function(_1zX,_1zY,_1zZ,_1A0,_1A1,_1A2,_1A3,_1A4,_1A5,_1A6,_1A7,_1A8,_){var _1A9=jsElemsByClassName(toJSStr(E(_1zV))),_1Aa=_1A9,_1Ab=B((function(_1Ac,_){while(1){var _1Ad=E(_1Ac);if(!_1Ad[0]){return _5c;}else{var _1Ae=B(_1zp(_1zX,_1zY,_1zZ,_1A0,_1A1,_1A2,_1A3,_1A4,_1A5,_1A6,_1A7,_1A8,E(_1Ad[1])[1],_)),_1Af=_1Ae;_1Ac=_1Ad[2];continue;}}})(_1Aa,_)),_1Ag=_1Ab,_1Ah=jsLog(toJSStr(E(_1zU))),_1Ai=jsSetTimeout(60,_1zR);return _5c;},_1Aj=new T(function(){return B(unCStr("ADD"));}),_1Ak=new T(function(){return B(unCStr("ADJ"));}),_1Al=[0,1],_1Am=[1,_1Al],_1An=[1,_1Am],_1Ao=[0,_1Al],_1Ap=[1,_1Ao],_1Aq=new T(function(){return B(unCStr("DN"));}),_1Ar=new T(function(){return B(_l0(_9,_1Aq));}),_1As=new T(function(){return B(unCStr("MTP"));}),_1At=new T(function(){return B(unCStr("MP"));}),_1Au=new T(function(){return B(unCStr("ID"));}),_1Av=new T(function(){return B(unCStr("CD"));}),_1Aw=[0,2],_1Ax=[1,_1Aw],_1Ay=[1,_1Ax],_1Az=[0,_1Aw],_1AA=[1,_1Az],_1AB=function(_1AC){if(!B(_l0(_1AC,_1Aj))){if(!B(_l0(_1AC,_1Ak))){if(!B(_l0(_1AC,_1Av))){if(!B(_l0(_1AC,_1Au))){if(!B(_l0(_1AC,_1At))){if(!B(_l0(_1AC,_1As))){var _1AD=E(_1AC);return _1AD[0]==0?!E(_1Ar)?[0]:E(_1Ap):E(E(_1AD[1])[1])==83?E(_1AD[2])[0]==0?E(_1Ap):!B(_l0(_1AD,_1Aq))?[0]:E(_1Ap):!B(_l0(_1AD,_1Aq))?[0]:E(_1Ap);}else{return E(_1AA);}}else{return E(_1AA);}}else{return E(_1Ay);}}else{return E(_1An);}}else{return E(_1AA);}}else{return E(_1Ap);}},_1AE=function(_1AF){return E(E(_1AF)[2]);},_1AG=function(_1AH,_1AI,_1AJ){while(1){var _1AK=E(_1AI);if(!_1AK[0]){return E(_1AJ)[0]==0?1:0;}else{var _1AL=E(_1AJ);if(!_1AL[0]){return 2;}else{var _1AM=B(A(_1AE,[_1AH,_1AK[1],_1AL[1]]));if(_1AM==1){_1AI=_1AK[2];_1AJ=_1AL[2];continue;}else{return E(_1AM);}}}}},_1AN=function(_1AO){return E(E(_1AO)[3]);},_1AP=function(_1AQ,_1AR,_1AS,_1AT,_1AU){switch(B(_1AG(_1AQ,_1AR,_1AT))){case 0:return true;case 1:return new F(function(){return A(_1AN,[_1AQ,_1AS,_1AU]);});break;default:return false;}},_1AV=function(_1AW,_1AX,_1AY,_1AZ){var _1B0=E(_1AY),_1B1=E(_1AZ);return new F(function(){return _1AP(_1AX,_1B0[1],_1B0[2],_1B1[1],_1B1[2]);});},_1B2=function(_1B3){return E(E(_1B3)[6]);},_1B4=function(_1B5,_1B6,_1B7,_1B8,_1B9){switch(B(_1AG(_1B5,_1B6,_1B8))){case 0:return true;case 1:return new F(function(){return A(_1B2,[_1B5,_1B7,_1B9]);});break;default:return false;}},_1Ba=function(_1Bb,_1Bc,_1Bd,_1Be){var _1Bf=E(_1Bd),_1Bg=E(_1Be);return new F(function(){return _1B4(_1Bc,_1Bf[1],_1Bf[2],_1Bg[1],_1Bg[2]);});},_1Bh=function(_1Bi){return E(E(_1Bi)[5]);},_1Bj=function(_1Bk,_1Bl,_1Bm,_1Bn,_1Bo){switch(B(_1AG(_1Bk,_1Bl,_1Bn))){case 0:return false;case 1:return new F(function(){return A(_1Bh,[_1Bk,_1Bm,_1Bo]);});break;default:return true;}},_1Bp=function(_1Bq,_1Br,_1Bs,_1Bt){var _1Bu=E(_1Bs),_1Bv=E(_1Bt);return new F(function(){return _1Bj(_1Br,_1Bu[1],_1Bu[2],_1Bv[1],_1Bv[2]);});},_1Bw=function(_1Bx){return E(E(_1Bx)[4]);},_1By=function(_1Bz,_1BA,_1BB,_1BC,_1BD){switch(B(_1AG(_1Bz,_1BA,_1BC))){case 0:return false;case 1:return new F(function(){return A(_1Bw,[_1Bz,_1BB,_1BD]);});break;default:return true;}},_1BE=function(_1BF,_1BG,_1BH,_1BI){var _1BJ=E(_1BH),_1BK=E(_1BI);return new F(function(){return _1By(_1BG,_1BJ[1],_1BJ[2],_1BK[1],_1BK[2]);});},_1BL=function(_1BM,_1BN,_1BO,_1BP,_1BQ){switch(B(_1AG(_1BM,_1BN,_1BP))){case 0:return 0;case 1:return new F(function(){return A(_1AE,[_1BM,_1BO,_1BQ]);});break;default:return 2;}},_1BR=function(_1BS,_1BT,_1BU,_1BV){var _1BW=E(_1BU),_1BX=E(_1BV);return new F(function(){return _1BL(_1BT,_1BW[1],_1BW[2],_1BX[1],_1BX[2]);});},_1BY=function(_1BZ,_1C0,_1C1,_1C2){var _1C3=E(_1C1),_1C4=_1C3[1],_1C5=_1C3[2],_1C6=E(_1C2),_1C7=_1C6[1],_1C8=_1C6[2];switch(B(_1AG(_1C0,_1C4,_1C7))){case 0:return [0,_1C7,_1C8];case 1:return !B(A(_1B2,[_1C0,_1C5,_1C8]))?[0,_1C4,_1C5]:[0,_1C7,_1C8];default:return [0,_1C4,_1C5];}},_1C9=function(_1Ca,_1Cb,_1Cc,_1Cd){var _1Ce=E(_1Cc),_1Cf=_1Ce[1],_1Cg=_1Ce[2],_1Ch=E(_1Cd),_1Ci=_1Ch[1],_1Cj=_1Ch[2];switch(B(_1AG(_1Cb,_1Cf,_1Ci))){case 0:return [0,_1Cf,_1Cg];case 1:return !B(A(_1B2,[_1Cb,_1Cg,_1Cj]))?[0,_1Ci,_1Cj]:[0,_1Cf,_1Cg];default:return [0,_1Ci,_1Cj];}},_1Ck=function(_1Cl,_1Cm){return [0,_1Cl,function(_Zq,_Zr){return new F(function(){return _1BR(_1Cl,_1Cm,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1AV(_1Cl,_1Cm,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1BE(_1Cl,_1Cm,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1Bp(_1Cl,_1Cm,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1Ba(_1Cl,_1Cm,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1BY(_1Cl,_1Cm,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1C9(_1Cl,_1Cm,_Zq,_Zr);});}];},_1Cn=function(_1Co,_1Cp,_1Cq,_1Cr){return !B(A(_1Co,[_1Cq,_1Cr]))?B(_cv(B(A(_1Cp,[_1Cq,_16l])),B(A(_1Cp,[_1Cr,_16l]))))==2?false:true:false;},_1Cs=function(_1Ct,_1Cu,_1Cv,_1Cw){return new F(function(){return _1Cn(E(_1Ct)[1],_1Cu,_1Cv,_1Cw);});},_1Cx=function(_1Cy,_1Cz,_1CA,_1CB){return B(_cv(B(A(_1Cz,[_1CA,_16l])),B(A(_1Cz,[_1CB,_16l]))))==2?false:true;},_1CC=function(_1CD,_1CE,_1CF,_1CG){return !B(A(_1CD,[_1CF,_1CG]))?B(_cv(B(A(_1CE,[_1CF,_16l])),B(A(_1CE,[_1CG,_16l]))))==2?true:false:false;},_1CH=function(_1CI,_1CJ,_1CK,_1CL){return new F(function(){return _1CC(E(_1CI)[1],_1CJ,_1CK,_1CL);});},_1CM=function(_1CN,_1CO,_1CP,_1CQ){return !B(A(_1CN,[_1CP,_1CQ]))?B(_cv(B(A(_1CO,[_1CP,_16l])),B(A(_1CO,[_1CQ,_16l]))))==2?true:false:true;},_1CR=function(_1CS,_1CT,_1CU,_1CV){return new F(function(){return _1CM(E(_1CS)[1],_1CT,_1CU,_1CV);});},_1CW=function(_1CX,_1CY,_1CZ,_1D0){return !B(A(_1CX,[_1CZ,_1D0]))?B(_cv(B(A(_1CY,[_1CZ,_16l])),B(A(_1CY,[_1D0,_16l]))))==2?2:0:1;},_1D1=function(_1D2,_1D3,_1D4,_1D5){return new F(function(){return _1CW(E(_1D2)[1],_1D3,_1D4,_1D5);});},_1D6=function(_1D7,_1D8,_1D9,_1Da){return B(_cv(B(A(_1D8,[_1D9,_16l])),B(A(_1D8,[_1Da,_16l]))))==2?E(_1D9):E(_1Da);},_1Db=function(_1Dc,_1Dd,_1De,_1Df){return B(_cv(B(A(_1Dd,[_1De,_16l])),B(A(_1Dd,[_1Df,_16l]))))==2?E(_1Df):E(_1De);},_1Dg=function(_1Dh,_1Di){return [0,_1Dh,function(_bi,_bj){return new F(function(){return _1D1(_1Dh,_1Di,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Cs(_1Dh,_1Di,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1CR(_1Dh,_1Di,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1CH(_1Dh,_1Di,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Cx(_1Dh,_1Di,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1D6(_1Dh,_1Di,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1Db(_1Dh,_1Di,_bi,_bj);});}];},_1Dj=function(_1Dk,_1Dl,_1Dm,_1Dn,_1Do,_1Dp,_1Dq){var _1Dr=function(_1Ds,_1Dt){return new F(function(){return _af(_1Dk,_1Dl,_1Dm,_1Do,_1Dn,_1Dq,_1Dp,_1Ds);});};return function(_1Du,_1Dv){var _1Dw=E(_1Du);if(!_1Dw[0]){var _1Dx=E(_1Dv);return _1Dx[0]==0?B(_cv(B(_a1(_1Dw[1])),B(_a1(_1Dx[1]))))==2?false:true:true;}else{var _1Dy=E(_1Dv);return _1Dy[0]==0?false:B(_1AG(new T(function(){return B(_1Dg(new T(function(){return B(_16q(_1Dr));}),_1Dr));}),_1Dw[1],_1Dy[1]))==2?false:true;}};},_1Dz=function(_1DA,_1DB,_1DC,_1DD,_1DE,_1DF,_1DG,_1DH,_1DI,_1DJ){return !B(A(_1Dj,[_1DB,_1DC,_1DD,_1DE,_1DF,_1DG,_1DH,_1DI,_1DJ]))?E(_1DI):E(_1DJ);},_1DK=function(_1DL,_1DM,_1DN,_1DO,_1DP,_1DQ,_1DR,_1DS,_1DT,_1DU){return !B(A(_1Dj,[_1DM,_1DN,_1DO,_1DP,_1DQ,_1DR,_1DS,_1DT,_1DU]))?E(_1DU):E(_1DT);},_1DV=function(_1DW,_1DX,_1DY,_1DZ,_1E0,_1E1,_1E2){var _1E3=function(_1E4,_1E5){return new F(function(){return _af(_1DW,_1DX,_1DY,_1E0,_1DZ,_1E2,_1E1,_1E4);});};return function(_1E6,_1E7){var _1E8=E(_1E6);if(!_1E8[0]){var _1E9=_1E8[1],_1Ea=E(_1E7);if(!_1Ea[0]){var _1Eb=_1Ea[1];return B(_108(_1E9,_1Eb,_1))[0]==0?B(_cv(B(_a1(_1E9)),B(_a1(_1Eb))))==2?false:true:false;}else{return true;}}else{var _1Ec=E(_1E7);return _1Ec[0]==0?false:B(_1AG(new T(function(){return B(_1Dg(new T(function(){return B(_16q(_1E3));}),_1E3));}),_1E8[1],_1Ec[1]))==0?true:false;}};},_1Ed=function(_1Ee,_1Ef,_1Eg,_1Eh,_1Ei,_1Ej,_1Ek){var _1El=function(_1Em,_1En){return new F(function(){return _af(_1Ee,_1Ef,_1Eg,_1Ei,_1Eh,_1Ek,_1Ej,_1Em);});};return function(_1Eo,_1Ep){var _1Eq=E(_1Eo);if(!_1Eq[0]){var _1Er=_1Eq[1],_1Es=E(_1Ep);if(!_1Es[0]){var _1Et=_1Es[1];return B(_108(_1Er,_1Et,_1))[0]==0?B(_cv(B(_a1(_1Er)),B(_a1(_1Et))))==2?true:false:false;}else{return false;}}else{var _1Eu=E(_1Ep);return _1Eu[0]==0?true:B(_1AG(new T(function(){return B(_1Dg(new T(function(){return B(_16q(_1El));}),_1El));}),_1Eq[1],_1Eu[1]))==2?true:false;}};},_1Ev=function(_1Ew,_1Ex,_1Ey,_1Ez,_1EA,_1EB,_1EC){var _1ED=function(_1EE,_1EF){return new F(function(){return _af(_1Ew,_1Ex,_1Ey,_1EA,_1Ez,_1EC,_1EB,_1EE);});};return function(_1EG,_1EH){var _1EI=E(_1EG);if(!_1EI[0]){var _1EJ=_1EI[1],_1EK=E(_1EH);if(!_1EK[0]){var _1EL=_1EK[1];return B(_108(_1EJ,_1EL,_1))[0]==0?B(_cv(B(_a1(_1EJ)),B(_a1(_1EL))))==2?true:false:true;}else{return false;}}else{var _1EM=E(_1EH);return _1EM[0]==0?true:B(_1AG(new T(function(){return B(_1Dg(new T(function(){return B(_16q(_1ED));}),_1ED));}),_1EI[1],_1EM[1]))==0?false:true;}};},_1EN=function(_1EO,_1EP,_1EQ,_1ER,_1ES,_1ET,_1EU){var _1EV=function(_1EW,_1EX){return new F(function(){return _af(_1EO,_1EP,_1EQ,_1ES,_1ER,_1EU,_1ET,_1EW);});};return function(_1EY,_1EZ){var _1F0=E(_1EY);if(!_1F0[0]){var _1F1=_1F0[1],_1F2=E(_1EZ);if(!_1F2[0]){var _1F3=_1F2[1];return B(_108(_1F1,_1F3,_1))[0]==0?B(_cv(B(_a1(_1F1)),B(_a1(_1F3))))==2?2:0:1;}else{return 0;}}else{var _1F4=E(_1EZ);return _1F4[0]==0?2:B(_1AG(new T(function(){return B(_1Dg(new T(function(){return B(_16q(_1EV));}),_1EV));}),_1F0[1],_1F4[1]));}};},_1F5=function(_1F6,_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_1Fd){return [0,_1F6,new T(function(){return B(_1EN(_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_1Fd));}),new T(function(){return B(_1DV(_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_1Fd));}),new T(function(){return B(_1Ev(_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_1Fd));}),new T(function(){return B(_1Ed(_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_1Fd));}),new T(function(){return B(_1Dj(_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_1Fd));}),function(_bi,_bj){return new F(function(){return _1Dz(_1F6,_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_1Fd,_bi,_bj);});},function(_bi,_bj){return new F(function(){return _1DK(_1F6,_1F7,_1F8,_1F9,_1Fa,_1Fb,_1Fc,_1Fd,_bi,_bj);});}];},_1Fe=new T(function(){return B(_ZM(_Q,_u,_Q,_Q,_N,_2,_15));}),_1Ff=new T(function(){return B(_1F5(_1Fe,_Q,_u,_Q,_Q,_N,_15,_2));}),_1Fg=new T(function(){return B(_106(_1Fe));}),_1Fh=new T(function(){return B(_1Ck(_1Fg,_1Ff));}),_1Fi=function(_1Fj,_1Fk,_1Fl,_1Fm){var _1Fn=E(_1Fl),_1Fo=E(_1Fm);return new F(function(){return _1AP(_1Fk,_1Fn[1],_1Fn[2],_1Fo[1],_1Fo[2]);});},_1Fp=function(_1Fq,_1Fr,_1Fs,_1Ft){var _1Fu=E(_1Fs),_1Fv=E(_1Ft);return new F(function(){return _1B4(_1Fr,_1Fu[1],_1Fu[2],_1Fv[1],_1Fv[2]);});},_1Fw=function(_1Fx,_1Fy,_1Fz,_1FA){var _1FB=E(_1Fz),_1FC=E(_1FA);return new F(function(){return _1Bj(_1Fy,_1FB[1],_1FB[2],_1FC[1],_1FC[2]);});},_1FD=function(_1FE,_1FF,_1FG,_1FH){var _1FI=E(_1FG),_1FJ=E(_1FH);return new F(function(){return _1By(_1FF,_1FI[1],_1FI[2],_1FJ[1],_1FJ[2]);});},_1FK=function(_1FL,_1FM,_1FN,_1FO){var _1FP=E(_1FN),_1FQ=E(_1FO);return new F(function(){return _1BL(_1FM,_1FP[1],_1FP[2],_1FQ[1],_1FQ[2]);});},_1FR=function(_1FS,_1FT,_1FU,_1FV){var _1FW=E(_1FU),_1FX=_1FW[1],_1FY=_1FW[2],_1FZ=E(_1FV),_1G0=_1FZ[1],_1G1=_1FZ[2];switch(B(_1AG(_1FT,_1FX,_1G0))){case 0:return [0,_1G0,_1G1];case 1:return !B(A(_1B2,[_1FT,_1FY,_1G1]))?[0,_1FX,_1FY]:[0,_1G0,_1G1];default:return [0,_1FX,_1FY];}},_1G2=function(_1G3,_1G4,_1G5,_1G6){var _1G7=E(_1G5),_1G8=_1G7[1],_1G9=_1G7[2],_1Ga=E(_1G6),_1Gb=_1Ga[1],_1Gc=_1Ga[2];switch(B(_1AG(_1G4,_1G8,_1Gb))){case 0:return [0,_1G8,_1G9];case 1:return !B(A(_1B2,[_1G4,_1G9,_1Gc]))?[0,_1Gb,_1Gc]:[0,_1G8,_1G9];default:return [0,_1Gb,_1Gc];}},_1Gd=function(_1Ge,_1Gf){return [0,_1Ge,function(_Zq,_Zr){return new F(function(){return _1FK(_1Ge,_1Gf,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1Fi(_1Ge,_1Gf,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1FD(_1Ge,_1Gf,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1Fw(_1Ge,_1Gf,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1Fp(_1Ge,_1Gf,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1FR(_1Ge,_1Gf,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1G2(_1Ge,_1Gf,_Zq,_Zr);});}];},_1Gg=function(_1Gh,_1Gi){return B(_cv(_1Gh,_1Gi))==0?false:true;},_1Gj=function(_1Gk){return E(E(_1Gk)[1]);},_1Gl=function(_1Gm){return function(_1Gn,_1Go){var _1Gp=E(_1Gn),_1Gq=E(_1Go);switch(B(_1AG(new T(function(){return B(_1Gd(new T(function(){return B(_Zo(new T(function(){return B(_1Gj(_1Gm));})));}),_1Gm));}),_1Gp[1],_1Gq[1]))){case 0:return false;case 1:return new F(function(){return _1Gg(_1Gp[2],_1Gq[2]);});break;default:return true;}};},_1Gr=new T(function(){return B(_1Gl(_1Fh));}),_1Gs=function(_1Gt,_1Gu,_1Gv){var _1Gw=E(_1Gt);if(_1Gw==1){var _1Gx=E(_1Gv);return _1Gx[0]==0?[0,new T(function(){return [0,1,E(E(_1Gu)),E(_1e3),E(_1e3)];}),_9,_9]:!B(A(_1Gr,[_1Gu,_1Gx[1]]))?[0,new T(function(){return [0,1,E(E(_1Gu)),E(_1e3),E(_1e3)];}),_1Gx,_9]:[0,new T(function(){return [0,1,E(E(_1Gu)),E(_1e3),E(_1e3)];}),_9,_1Gx];}else{var _1Gy=B(_1Gs(_1Gw>>1,_1Gu,_1Gv)),_1Gz=_1Gy[1],_1GA=_1Gy[3],_1GB=E(_1Gy[2]);if(!_1GB[0]){return [0,_1Gz,_9,_1GA];}else{var _1GC=_1GB[1],_1GD=E(_1GB[2]);if(!_1GD[0]){return [0,new T(function(){return B(_1fq(_1GC,_1Gz));}),_9,_1GA];}else{var _1GE=_1GD[1];if(!B(A(_1Gr,[_1GC,_1GE]))){var _1GF=B(_1Gs(_1Gw>>1,_1GE,_1GD[2]));return [0,new T(function(){return B(_1g4(_1GC,_1Gz,_1GF[1]));}),_1GF[2],_1GF[3]];}else{return [0,_1Gz,_9,_1GB];}}}}},_1GG=function(_1GH,_1GI){return B(_cv(_1GH,_1GI))==2?false:true;},_1GJ=function(_1GK){return function(_1GL,_1GM){var _1GN=E(_1GL),_1GO=E(_1GM);switch(B(_1AG(new T(function(){return B(_1Gd(new T(function(){return B(_Zo(new T(function(){return B(_1Gj(_1GK));})));}),_1GK));}),_1GN[1],_1GO[1]))){case 0:return true;case 1:return new F(function(){return _1GG(_1GN[2],_1GO[2]);});break;default:return false;}};},_1GP=function(_1GQ,_1GR,_1GS,_1GT){return !B(A(_1GJ,[_1GR,_1GS,_1GT]))?E(_1GS):E(_1GT);},_1GU=function(_1GV,_1GW,_1GX,_1GY){return !B(A(_1GJ,[_1GW,_1GX,_1GY]))?E(_1GY):E(_1GX);},_1GZ=function(_1H0,_1H1){return B(_cv(_1H0,_1H1))==0?true:false;},_1H2=function(_1H3){return function(_1H4,_1H5){var _1H6=E(_1H4),_1H7=E(_1H5);switch(B(_1AG(new T(function(){return B(_1Gd(new T(function(){return B(_Zo(new T(function(){return B(_1Gj(_1H3));})));}),_1H3));}),_1H6[1],_1H7[1]))){case 0:return true;case 1:return new F(function(){return _1GZ(_1H6[2],_1H7[2]);});break;default:return false;}};},_1H8=function(_1H9,_1Ha){return B(_cv(_1H9,_1Ha))==2?true:false;},_1Hb=function(_1Hc){return function(_1Hd,_1He){var _1Hf=E(_1Hd),_1Hg=E(_1He);switch(B(_1AG(new T(function(){return B(_1Gd(new T(function(){return B(_Zo(new T(function(){return B(_1Gj(_1Hc));})));}),_1Hc));}),_1Hf[1],_1Hg[1]))){case 0:return false;case 1:return new F(function(){return _1H8(_1Hf[2],_1Hg[2]);});break;default:return true;}};},_1Hh=function(_1Hi){return function(_1Hj,_1Hk){var _1Hl=E(_1Hj),_1Hm=E(_1Hk);switch(B(_1AG(new T(function(){return B(_1Gd(new T(function(){return B(_Zo(new T(function(){return B(_1Gj(_1Hi));})));}),_1Hi));}),_1Hl[1],_1Hm[1]))){case 0:return 0;case 1:return new F(function(){return _cv(_1Hl[2],_1Hm[2]);});break;default:return 2;}};},_1Hn=function(_1Ho,_1Hp){return [0,_1Ho,new T(function(){return B(_1Hh(_1Hp));}),new T(function(){return B(_1H2(_1Hp));}),new T(function(){return B(_1Gl(_1Hp));}),new T(function(){return B(_1Hb(_1Hp));}),new T(function(){return B(_1GJ(_1Hp));}),function(_Zq,_Zr){return new F(function(){return _1GP(_1Ho,_1Hp,_Zq,_Zr);});},function(_Zq,_Zr){return new F(function(){return _1GU(_1Ho,_1Hp,_Zq,_Zr);});}];},_1Hq=function(_1Hr,_1Hs,_1Ht,_1Hu,_1Hv){return !B(_Z0(new T(function(){return B(_Zo(_1Hr));}),_1Hs,_1Hu))?true:!B(_l0(_1Ht,_1Hv))?true:false;},_1Hw=function(_1Hx,_1Hy,_1Hz){var _1HA=E(_1Hy),_1HB=E(_1Hz);return new F(function(){return _1Hq(_1Hx,_1HA[1],_1HA[2],_1HB[1],_1HB[2]);});},_1HC=function(_1HD){return function(_1HE,_1HF){var _1HG=E(_1HE),_1HH=E(_1HF);return !B(_Z0(new T(function(){return B(_Zo(_1HD));}),_1HG[1],_1HH[1]))?false:B(_l0(_1HG[2],_1HH[2]));};},_1HI=function(_1HJ){return [0,new T(function(){return B(_1HC(_1HJ));}),function(_Zq,_Zr){return new F(function(){return _1Hw(_1HJ,_Zq,_Zr);});}];},_1HK=new T(function(){return B(_1HI(_1Fg));}),_1HL=new T(function(){return B(_1Hn(_1HK,_1Fh));}),_1HM=function(_1HN,_1HO,_1HP){var _1HQ=E(_1HO),_1HR=E(_1HP);if(!_1HR[0]){var _1HS=_1HR[2],_1HT=_1HR[3],_1HU=_1HR[4];switch(B(A(_1AE,[_1HN,_1HQ,_1HS]))){case 0:return new F(function(){return _1e8(_1HS,B(_1HM(_1HN,_1HQ,_1HT)),_1HU);});break;case 1:return [0,_1HR[1],E(_1HQ),E(_1HT),E(_1HU)];default:return new F(function(){return _1eK(_1HS,_1HT,B(_1HM(_1HN,_1HQ,_1HU)));});}}else{return [0,1,E(_1HQ),E(_1e3),E(_1e3)];}},_1HV=function(_1HW,_1HX){while(1){var _1HY=E(_1HX);if(!_1HY[0]){return E(_1HW);}else{var _1HZ=B(_1HM(_1HL,_1HY[1],_1HW));_1HX=_1HY[2];_1HW=_1HZ;continue;}}},_1I0=function(_1I1,_1I2,_1I3){return new F(function(){return _1HV(B(_1HM(_1HL,_1I2,_1I1)),_1I3);});},_1I4=function(_1I5,_1I6,_1I7){while(1){var _1I8=E(_1I7);if(!_1I8[0]){return E(_1I6);}else{var _1I9=_1I8[1],_1Ia=E(_1I8[2]);if(!_1Ia[0]){return new F(function(){return _1fq(_1I9,_1I6);});}else{var _1Ib=_1Ia[1];if(!B(A(_1Gr,[_1I9,_1Ib]))){var _1Ic=B(_1Gs(_1I5,_1Ib,_1Ia[2])),_1Id=_1Ic[1],_1Ie=E(_1Ic[3]);if(!_1Ie[0]){var _1If=_1I5<<1,_1Ig=B(_1g4(_1I9,_1I6,_1Id));_1I7=_1Ic[2];_1I5=_1If;_1I6=_1Ig;continue;}else{return new F(function(){return _1I0(B(_1g4(_1I9,_1I6,_1Id)),_1Ie[1],_1Ie[2]);});}}else{return new F(function(){return _1I0(_1I6,_1I9,_1Ia);});}}}}},_1Ih=function(_1Ii,_1Ij,_1Ik,_1Il){var _1Im=E(_1Il);if(!_1Im[0]){return new F(function(){return _1fq(_1Ik,_1Ij);});}else{var _1In=_1Im[1];if(!B(A(_1Gr,[_1Ik,_1In]))){var _1Io=B(_1Gs(_1Ii,_1In,_1Im[2])),_1Ip=_1Io[1],_1Iq=E(_1Io[3]);if(!_1Iq[0]){return new F(function(){return _1I4(_1Ii<<1,B(_1g4(_1Ik,_1Ij,_1Ip)),_1Io[2]);});}else{return new F(function(){return _1I0(B(_1g4(_1Ik,_1Ij,_1Ip)),_1Iq[1],_1Iq[2]);});}}else{return new F(function(){return _1I0(_1Ij,_1Ik,_1Im);});}}},_1Ir=function(_1Is){var _1It=E(_1Is);if(!_1It[0]){return [1];}else{var _1Iu=_1It[1],_1Iv=E(_1It[2]);if(!_1Iv[0]){return [0,1,E(E(_1Iu)),E(_1e3),E(_1e3)];}else{var _1Iw=_1Iv[1],_1Ix=_1Iv[2];if(!B(A(_1Gr,[_1Iu,_1Iw]))){return new F(function(){return _1Ih(1,[0,1,E(E(_1Iu)),E(_1e3),E(_1e3)],_1Iw,_1Ix);});}else{return new F(function(){return _1I0([0,1,E(E(_1Iu)),E(_1e3),E(_1e3)],_1Iw,_1Ix);});}}}},_1Iy=new T(function(){return B(_F(0,1,_9));}),_1Iz=new T(function(){return B(unAppCStr("delta_",_1Iy));}),_1IA=[9,_,_,_1Iz],_1IB=[0,_1IA],_1IC=[1,_1IB,_9],_1ID=new T(function(){return B(unAppCStr("phi_",_1Iy));}),_1IE=[3,_,_,_1ID],_1IF=[2,_,_1IE],_1IG=[1,_1IF,_9],_1IH=[1,_1IG],_1II=[0,_1IC,_1IH],_1IJ=new T(function(){return B(_F(0,2,_9));}),_1IK=new T(function(){return B(unAppCStr("phi_",_1IJ));}),_1IL=[3,_,_,_1IK],_1IM=[2,_,_1IL],_1IN=[1,_1IM,_9],_1IO=[1,_1IN],_1IP=new T(function(){return B(unAppCStr("delta_",_1IJ));}),_1IQ=[9,_,_,_1IP],_1IR=[0,_1IQ],_1IS=[1,_1IR,_9],_1IT=[0,_1IS,_1IO],_1IU=[1,_1IT,_9],_1IV=[1,_1II,_1IU],_1IW=[9,_,_OF,_1IF,_1IM],_1IX=[1,_1IW,_9],_1IY=[1,_1IX],_1IZ=[1,_1IB,_1IS],_1J0=[0,_1IZ,_1IY],_1J1=[0,_1IV,_1J0],_1J2=[0,_1IS,_1IH],_1J3=[1,_1J2,_9],_1J4=[0,_1IC,_1IO],_1J5=[1,_1J4,_1J3],_1J6=[0,_1J5,_1J0],_1J7=[1,_1J6,_9],_1J8=[1,_1J1,_1J7],_1J9=[0,_1J8,_1Ak],_1Ja=[1,_1II,_9],_1Jb=[9,_,_Oh,_1IF,_1IM],_1Jc=[1,_1Jb,_9],_1Jd=[1,_1Jc],_1Je=[0,_1IC,_1Jd],_1Jf=[0,_1Ja,_1Je],_1Jg=[9,_,_Oh,_1IM,_1IF],_1Jh=[1,_1Jg,_9],_1Ji=[1,_1Jh],_1Jj=[0,_1IC,_1Ji],_1Jk=[0,_1Ja,_1Jj],_1Jl=[1,_1Jk,_9],_1Jm=[1,_1Jf,_1Jl],_1Jn=[0,_1Jm,_1Aj],_1Jo=[1,_1IH,_1IS],_1Jp=[7,_,_P6,_1IM],_1Jq=[1,_1Jp,_9],_1Jr=[1,_1Jq],_1Js=[0,_1Jo,_1Jr],_1Jt=[1,_1Js,_9],_1Ju=[1,_1IH,_1IC],_1Jv=[0,_1Ju,_1IO],_1Jw=[1,_1Jv,_1Jt],_1Jx=[7,_,_P6,_1IF],_1Jy=[1,_1Jx,_9],_1Jz=[1,_1Jy],_1JA=[0,_1IZ,_1Jz],_1JB=[0,_1Jw,_1JA],_1JC=[1,_1J4,_1Jt],_1JD=[0,_1JC,_1JA],_1JE=[0,_1IS,_1Jr],_1JF=[1,_1JE,_9],_1JG=[1,_1Jv,_1JF],_1JH=[0,_1JG,_1JA],_1JI=[1,_1J4,_1JF],_1JJ=[0,_1JI,_1JA],_1JK=[1,_1Jv,_9],_1JL=[1,_1Js,_1JK],_1JM=[0,_1JL,_1JA],_1JN=[1,_1JE,_1JK],_1JO=[0,_1JN,_1JA],_1JP=[1,_1J4,_9],_1JQ=[1,_1Js,_1JP],_1JR=[0,_1JQ,_1JA],_1JS=[1,_1JE,_1JP],_1JT=[0,_1JS,_1JA],_1JU=[1,_1Jz,_1IS],_1JV=[0,_1JU,_1Jr],_1JW=[1,_1Jz,_1IC],_1JX=[0,_1JW,_1IO],_1JY=[1,_1JX,_9],_1JZ=[1,_1JV,_1JY],_1K0=[0,_1IZ,_1IH],_1K1=[0,_1JZ,_1K0],_1K2=[1,_1JE,_1JY],_1K3=[0,_1K2,_1K0],_1K4=[1,_1JV,_1JP],_1K5=[0,_1K4,_1K0],_1K6=[0,_1JS,_1K0],_1K7=[1,_1K6,_9],_1K8=[1,_1K5,_1K7],_1K9=[1,_1K3,_1K8],_1Ka=[1,_1K1,_1K9],_1Kb=[1,_1JT,_1Ka],_1Kc=[1,_1JR,_1Kb],_1Kd=[1,_1JO,_1Kc],_1Ke=[1,_1JM,_1Kd],_1Kf=[1,_1JJ,_1Ke],_1Kg=[1,_1JH,_1Kf],_1Kh=[1,_1JD,_1Kg],_1Ki=[1,_1JB,_1Kh],_1Kj=[0,_1Ki,_1Au],_1Kk=[1,_1Kj,_9],_1Kl=[1,_1Jn,_1Kk],_1Km=[0,83],_1Kn=[1,_1Km,_9],_1Ko=[0,_1IC,_1IY],_1Kp=[1,_1Ko,_9],_1Kq=[0,_1Kp,_1II],_1Kr=[0,_1Kp,_1J4],_1Ks=[1,_1Kr,_9],_1Kt=[1,_1Kq,_1Ks],_1Ku=[0,_1Kt,_1Kn],_1Kv=[1,_1Ku,_1Kl],_1Kw=[0,_1IZ,_1IO],_1Kx=[0,_1IS,_1Jz],_1Ky=[1,_1Kx,_9],_1Kz=[1,_1Jj,_1Ky],_1KA=[0,_1Kz,_1Kw],_1KB=[1,_1Jj,_9],_1KC=[1,_1Kx,_1KB],_1KD=[0,_1KC,_1Kw],_1KE=[1,_1KA,_9],_1KF=[1,_1KD,_1KE],_1KG=[1,_1KA,_1KF],_1KH=[1,_1KA,_1KG],_1KI=[0,_1KH,_1As],_1KJ=[1,_1KI,_1Kv],_1KK=[9,_,_N5,_1IF,_1IM],_1KL=[1,_1KK,_9],_1KM=[1,_1KL],_1KN=[0,_1IS,_1KM],_1KO=[1,_1KN,_9],_1KP=[1,_1II,_1KO],_1KQ=[0,_1KP,_1Kw],_1KR=[0,_1IC,_1KM],_1KS=[1,_1KR,_1J3],_1KT=[0,_1KS,_1Kw],_1KU=[1,_1KT,_9],_1KV=[1,_1KQ,_1KU],_1KW=[0,_1KV,_1At],_1KX=[1,_1KW,_1KJ],_1KY=[0,_1JK,_1KR],_1KZ=[0,_1JP,_1KR],_1L0=[1,_1KZ,_9],_1L1=[1,_1KY,_1L0],_1L2=[0,_1L1,_1Av],_1L3=[1,_1L2,_1KX],_1L4=[1,_1J9,_1L3],_1L5=new T(function(){return B(_1Ir(_1L4));}),_1L6=[0,_1AB,_1L5],_1L7=function(_){return new F(function(){return _1zW(_2,_15,_N,_Q,_Q,_u,_Q,_11,_1d,_17,_1g,_1L6,_);});},_1L8=function(_){return new F(function(){return _1L7(_);});};
var hasteMain = function() {B(A(_1L8, [0]));};window.onload = hasteMain;