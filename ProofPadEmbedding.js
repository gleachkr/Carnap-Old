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

var _0=0,_1=function(_){var _2=jsEval("$(\".lined\").linedtextarea({selectedLine:1});"),_3=_2;return _0;},_4=function(_5,_6,_){var _7=jsGet(_5,toJSStr(E(_6))),_8=_7;return new T(function(){return fromJSStr(_8);});},_9=function(_a,_b,_c,_d){return new F(function(){return A(_a,[function(_){var _e=jsSet(E(_b)[1],toJSStr(E(_c)),toJSStr(E(_d)));return _0;}]);});},_f=[0],_g=[13,_],_h=new T(function(){return B(unCStr("wheel"));}),_i=new T(function(){return B(unCStr("mouseout"));}),_j=new T(function(){return B(unCStr("mouseover"));}),_k=new T(function(){return B(unCStr("mousemove"));}),_l=new T(function(){return B(unCStr("blur"));}),_m=new T(function(){return B(unCStr("focus"));}),_n=new T(function(){return B(unCStr("change"));}),_o=new T(function(){return B(unCStr("unload"));}),_p=new T(function(){return B(unCStr("load"));}),_q=new T(function(){return B(unCStr("submit"));}),_r=new T(function(){return B(unCStr("keydown"));}),_s=new T(function(){return B(unCStr("keyup"));}),_t=new T(function(){return B(unCStr("keypress"));}),_u=new T(function(){return B(unCStr("mouseup"));}),_v=new T(function(){return B(unCStr("mousedown"));}),_w=new T(function(){return B(unCStr("dblclick"));}),_x=new T(function(){return B(unCStr("click"));}),_y=function(_z){switch(E(_z)[0]){case 0:return E(_p);case 1:return E(_o);case 2:return E(_n);case 3:return E(_m);case 4:return E(_l);case 5:return E(_k);case 6:return E(_j);case 7:return E(_i);case 8:return E(_x);case 9:return E(_w);case 10:return E(_v);case 11:return E(_u);case 12:return E(_t);case 13:return E(_s);case 14:return E(_r);case 15:return E(_q);default:return E(_h);}},_A=new T(function(){return B(unCStr("Haste.HPlay.View"));}),_B=new T(function(){return B(unCStr("hplayground-0.1.2.2"));}),_C=new T(function(){return B(unCStr("EventData"));}),_D=new T(function(){var _E=hs_wordToWord64(736961551),_F=_E,_G=hs_wordToWord64(735248784),_H=_G;return [0,_F,_H,[0,_F,_H,_B,_A,_C],_f];}),_I=[0,0],_J=false,_K=2,_L=[1],_M=new T(function(){return B(unCStr("Dynamic"));}),_N=new T(function(){return B(unCStr("Data.Dynamic"));}),_O=new T(function(){return B(unCStr("base"));}),_P=new T(function(){var _Q=hs_wordToWord64(628307645),_R=_Q,_S=hs_wordToWord64(949574464),_T=_S;return [0,_R,_T,[0,_R,_T,_O,_N,_M],_f];}),_U=[0],_V=new T(function(){return B(unCStr("OnLoad"));}),_W=[0,_V,_U],_X=[0,_D,_W],_Y=[0,_P,_X],_Z=[0],_10=function(_){return _Z;},_11=function(_12,_){return _Z;},_13=[0,_10,_11],_14=[0,_f,_I,_K,_13,_J,_Y,_L],_15=function(_){var _=0,_16=newMVar(),_17=_16,_=putMVar(_17,_14);return [0,_17];},_18=function(_19){var _1a=B(A(_19,[_])),_1b=_1a;return E(_1b);},_1c=new T(function(){return B(_18(_15));}),_1d=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1e=new T(function(){return B(unCStr("base"));}),_1f=new T(function(){return B(unCStr("PatternMatchFail"));}),_1g=new T(function(){var _1h=hs_wordToWord64(18445595),_1i=_1h,_1j=hs_wordToWord64(52003073),_1k=_1j;return [0,_1i,_1k,[0,_1i,_1k,_1e,_1d,_1f],_f];}),_1l=function(_1m){return E(_1g);},_1n=function(_1o){return E(E(_1o)[1]);},_1p=function(_1q,_1r,_1s){var _1t=B(A(_1q,[_])),_1u=B(A(_1r,[_])),_1v=hs_eqWord64(_1t[1],_1u[1]),_1w=_1v;if(!E(_1w)){return [0];}else{var _1x=hs_eqWord64(_1t[2],_1u[2]),_1y=_1x;return E(_1y)==0?[0]:[1,_1s];}},_1z=function(_1A){var _1B=E(_1A);return new F(function(){return _1p(B(_1n(_1B[1])),_1l,_1B[2]);});},_1C=function(_1D){return E(E(_1D)[1]);},_1E=function(_1F,_1G){var _1H=E(_1F);return _1H[0]==0?E(_1G):[1,_1H[1],new T(function(){return B(_1E(_1H[2],_1G));})];},_1I=function(_1J,_1K){return new F(function(){return _1E(E(_1J)[1],_1K);});},_1L=[0,44],_1M=[0,93],_1N=[0,91],_1O=function(_1P,_1Q,_1R){var _1S=E(_1Q);return _1S[0]==0?B(unAppCStr("[]",_1R)):[1,_1N,new T(function(){return B(A(_1P,[_1S[1],new T(function(){var _1T=function(_1U){var _1V=E(_1U);return _1V[0]==0?E([1,_1M,_1R]):[1,_1L,new T(function(){return B(A(_1P,[_1V[1],new T(function(){return B(_1T(_1V[2]));})]));})];};return B(_1T(_1S[2]));})]));})];},_1W=function(_1X,_1Y){return new F(function(){return _1O(_1I,_1X,_1Y);});},_1Z=function(_20,_21,_22){return new F(function(){return _1E(E(_21)[1],_22);});},_23=[0,_1Z,_1C,_1W],_24=new T(function(){return [0,_1l,_23,_25,_1z];}),_25=function(_26){return [0,_24,_26];},_27=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_28=function(_29,_2a){return new F(function(){return die(new T(function(){return B(A(_2a,[_29]));}));});},_2b=function(_2c,_2d){var _2e=E(_2d);if(!_2e[0]){return [0,_f,_f];}else{var _2f=_2e[1];if(!B(A(_2c,[_2f]))){return [0,_f,_2e];}else{var _2g=new T(function(){var _2h=B(_2b(_2c,_2e[2]));return [0,_2h[1],_2h[2]];});return [0,[1,_2f,new T(function(){return E(E(_2g)[1]);})],new T(function(){return E(E(_2g)[2]);})];}}},_2i=[0,32],_2j=[0,10],_2k=[1,_2j,_f],_2l=function(_2m){return E(E(_2m)[1])==124?false:true;},_2n=function(_2o,_2p){var _2q=B(_2b(_2l,B(unCStr(_2o)))),_2r=_2q[1],_2s=function(_2t,_2u){return new F(function(){return _1E(_2t,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_1E(_2p,new T(function(){return B(_1E(_2u,_2k));},1)));})));},1));});},_2v=E(_2q[2]);if(!_2v[0]){return new F(function(){return _2s(_2r,_f);});}else{return E(E(_2v[1])[1])==124?B(_2s(_2r,[1,_2i,_2v[2]])):B(_2s(_2r,_f));}},_2w=function(_2x){return new F(function(){return _28([0,new T(function(){return B(_2n(_2x,_27));})],_25);});},_2y=new T(function(){return B(_2w("src/Haste/HPlay/View.hs:(1066,9)-(1100,63)|case"));}),_2z=[0,_p,_U],_2A=[0,_D,_2z],_2B=[0,_o,_U],_2C=[0,_D,_2B],_2D=[0,_n,_U],_2E=[0,_D,_2D],_2F=[0,_m,_U],_2G=[0,_D,_2F],_2H=[0,_l,_U],_2I=[0,_D,_2H],_2J=[3],_2K=[0,_i,_2J],_2L=[0,_D,_2K],_2M=function(_2N,_2O){switch(E(_2N)[0]){case 0:return function(_){var _2P=E(_1c)[1],_2Q=takeMVar(_2P),_2R=_2Q,_=putMVar(_2P,new T(function(){var _2S=E(_2R);return [0,_2S[1],_2S[2],_2S[3],_2S[4],_2S[5],_2A,_2S[7]];}));return new F(function(){return A(_2O,[_]);});};case 1:return function(_){var _2T=E(_1c)[1],_2U=takeMVar(_2T),_2V=_2U,_=putMVar(_2T,new T(function(){var _2W=E(_2V);return [0,_2W[1],_2W[2],_2W[3],_2W[4],_2W[5],_2C,_2W[7]];}));return new F(function(){return A(_2O,[_]);});};case 2:return function(_){var _2X=E(_1c)[1],_2Y=takeMVar(_2X),_2Z=_2Y,_=putMVar(_2X,new T(function(){var _30=E(_2Z);return [0,_30[1],_30[2],_30[3],_30[4],_30[5],_2E,_30[7]];}));return new F(function(){return A(_2O,[_]);});};case 3:return function(_){var _31=E(_1c)[1],_32=takeMVar(_31),_33=_32,_=putMVar(_31,new T(function(){var _34=E(_33);return [0,_34[1],_34[2],_34[3],_34[4],_34[5],_2G,_34[7]];}));return new F(function(){return A(_2O,[_]);});};case 4:return function(_){var _35=E(_1c)[1],_36=takeMVar(_35),_37=_36,_=putMVar(_35,new T(function(){var _38=E(_37);return [0,_38[1],_38[2],_38[3],_38[4],_38[5],_2I,_38[7]];}));return new F(function(){return A(_2O,[_]);});};case 5:return function(_39){return function(_){var _3a=E(_1c)[1],_3b=takeMVar(_3a),_3c=_3b,_=putMVar(_3a,new T(function(){var _3d=E(_3c);return [0,_3d[1],_3d[2],_3d[3],_3d[4],_3d[5],[0,_D,[0,_k,[2,E(_39)]]],_3d[7]];}));return new F(function(){return A(_2O,[_]);});};};case 6:return function(_3e){return function(_){var _3f=E(_1c)[1],_3g=takeMVar(_3f),_3h=_3g,_=putMVar(_3f,new T(function(){var _3i=E(_3h);return [0,_3i[1],_3i[2],_3i[3],_3i[4],_3i[5],[0,_D,[0,_j,[2,E(_3e)]]],_3i[7]];}));return new F(function(){return A(_2O,[_]);});};};case 7:return function(_){var _3j=E(_1c)[1],_3k=takeMVar(_3j),_3l=_3k,_=putMVar(_3j,new T(function(){var _3m=E(_3l);return [0,_3m[1],_3m[2],_3m[3],_3m[4],_3m[5],_2L,_3m[7]];}));return new F(function(){return A(_2O,[_]);});};case 8:return function(_3n,_3o){return function(_){var _3p=E(_1c)[1],_3q=takeMVar(_3p),_3r=_3q,_=putMVar(_3p,new T(function(){var _3s=E(_3r);return [0,_3s[1],_3s[2],_3s[3],_3s[4],_3s[5],[0,_D,[0,_x,[1,_3n,E(_3o)]]],_3s[7]];}));return new F(function(){return A(_2O,[_]);});};};case 9:return function(_3t,_3u){return function(_){var _3v=E(_1c)[1],_3w=takeMVar(_3v),_3x=_3w,_=putMVar(_3v,new T(function(){var _3y=E(_3x);return [0,_3y[1],_3y[2],_3y[3],_3y[4],_3y[5],[0,_D,[0,_w,[1,_3t,E(_3u)]]],_3y[7]];}));return new F(function(){return A(_2O,[_]);});};};case 10:return function(_3z,_3A){return function(_){var _3B=E(_1c)[1],_3C=takeMVar(_3B),_3D=_3C,_=putMVar(_3B,new T(function(){var _3E=E(_3D);return [0,_3E[1],_3E[2],_3E[3],_3E[4],_3E[5],[0,_D,[0,_v,[1,_3z,E(_3A)]]],_3E[7]];}));return new F(function(){return A(_2O,[_]);});};};case 11:return function(_3F,_3G){return function(_){var _3H=E(_1c)[1],_3I=takeMVar(_3H),_3J=_3I,_=putMVar(_3H,new T(function(){var _3K=E(_3J);return [0,_3K[1],_3K[2],_3K[3],_3K[4],_3K[5],[0,_D,[0,_u,[1,_3F,E(_3G)]]],_3K[7]];}));return new F(function(){return A(_2O,[_]);});};};case 12:return function(_3L,_){var _3M=E(_1c)[1],_3N=takeMVar(_3M),_3O=_3N,_=putMVar(_3M,new T(function(){var _3P=E(_3O);return [0,_3P[1],_3P[2],_3P[3],_3P[4],_3P[5],[0,_D,[0,_t,[4,_3L]]],_3P[7]];}));return new F(function(){return A(_2O,[_]);});};case 13:return function(_3Q,_){var _3R=E(_1c)[1],_3S=takeMVar(_3R),_3T=_3S,_=putMVar(_3R,new T(function(){var _3U=E(_3T);return [0,_3U[1],_3U[2],_3U[3],_3U[4],_3U[5],[0,_D,[0,_s,[4,_3Q]]],_3U[7]];}));return new F(function(){return A(_2O,[_]);});};case 14:return function(_3V,_){var _3W=E(_1c)[1],_3X=takeMVar(_3W),_3Y=_3X,_=putMVar(_3W,new T(function(){var _3Z=E(_3Y);return [0,_3Z[1],_3Z[2],_3Z[3],_3Z[4],_3Z[5],[0,_D,[0,_r,[4,_3V]]],_3Z[7]];}));return new F(function(){return A(_2O,[_]);});};default:return E(_2y);}},_40=[0,_y,_2M],_41=function(_42,_43,_44,_45){return new F(function(){return A(_42,[function(_){var _46=jsSetAttr(E(_43)[1],toJSStr(E(_44)),toJSStr(E(_45)));return _0;}]);});},_47=function(_48,_49){var _4a=jsShowI(_48),_4b=_4a;return new F(function(){return _1E(fromJSStr(_4b),_49);});},_4c=[0,41],_4d=[0,40],_4e=function(_4f,_4g,_4h){if(_4g>=0){return new F(function(){return _47(_4g,_4h);});}else{return _4f<=6?B(_47(_4g,_4h)):[1,_4d,new T(function(){var _4i=jsShowI(_4g),_4j=_4i;return B(_1E(fromJSStr(_4j),[1,_4c,_4h]));})];}},_4k=[0,112],_4l=function(_4m){var _4n=new T(function(){return E(E(_4m)[2]);});return function(_4o,_){return [0,[1,_4k,new T(function(){return B(_1E(B(_4e(0,E(_4n)[1],_f)),new T(function(){return E(E(_4m)[1]);},1)));})],new T(function(){var _4p=E(_4m);return [0,_4p[1],new T(function(){return [0,E(_4n)[1]+1|0];}),_4p[3],_4p[4],_4p[5],_4p[6],_4p[7]];})];};},_4q=new T(function(){return B(unCStr("id"));}),_4r=function(_4s){return E(_4s);},_4t=new T(function(){return B(unCStr("noid"));}),_4u=function(_4v,_){return _4v;},_4w=function(_4x,_4y,_){var _4z=jsFind(toJSStr(E(_4y))),_4A=_4z,_4B=E(_4A);if(!_4B[0]){var _4C=E(_1c)[1],_4D=takeMVar(_4C),_4E=_4D,_4F=B(A(_4x,[_4E,_])),_4G=_4F,_4H=E(_4G),_=putMVar(_4C,_4H[2]);return E(_4H[1])[2];}else{var _4I=E(_4B[1]),_4J=jsClearChildren(_4I[1]),_4K=E(_1c)[1],_4L=takeMVar(_4K),_4M=_4L,_4N=B(A(_4x,[_4M,_])),_4O=_4N,_4P=E(_4O),_4Q=E(_4P[1]),_=putMVar(_4K,_4P[2]),_4R=B(A(_4Q[1],[_4I,_])),_4S=_4R;return _4Q[2];}},_4T=new T(function(){return B(unCStr("span"));}),_4U=function(_4V,_4W,_4X,_){var _4Y=jsCreateElem(toJSStr(E(_4T))),_4Z=_4Y,_50=jsAppendChild(_4Z,E(_4X)[1]),_51=[0,_4Z],_52=B(A(_4V,[_4W,_51,_])),_53=_52;return _51;},_54=function(_55){return E(_55);},_56=function(_57,_58,_59,_){var _5a=B(A(_4l,[_59,_59,_])),_5b=_5a,_5c=E(_5b),_5d=_5c[1],_5e=E(_5c[2]),_5f=_5e[2],_5g=E(_5e[4]),_5h=B(A(_57,[[0,_5e[1],_5f,_5e[3],[0,function(_){return new F(function(){return _4w(function(_5i,_){var _5j=B(A(_57,[new T(function(){var _5k=E(_5i);return [0,_5k[1],_5f,_5k[3],_5k[4],_5k[5],_5k[6],_5k[7]];}),_])),_5l=_5j;return [0,[0,_4u,E(E(_5l)[1])[2]],_5i];},_4t,_);});},function(_5m,_){var _5n=B(_4w(new T(function(){return B(A(_58,[_5m]));},1),_5d,_)),_5o=_5n,_5p=E(_5o);return _5p[0]==0?_Z:B(A(_5g[2],[_5p[1],_]));}],_5e[5],_5e[6],_5e[7]],_])),_5q=_5h,_5r=E(_5q),_5s=_5r[2],_5t=E(_5r[1]),_5u=_5t[1],_5v=E(_5t[2]);if(!_5v[0]){return [0,[0,function(_5w,_){var _5x=B(A(_5u,[_5w,_])),_5y=_5x;if(!E(E(_59)[5])){var _5z=B(_4U(_54,_4u,_5w,_)),_5A=_5z,_5B=B(A(_41,[_4r,_5A,_4q,_5d,_])),_5C=_5B;return _5w;}else{return _5w;}},_Z],new T(function(){var _5D=E(_5s);return [0,_5D[1],_5D[2],_5D[3],_5g,_5D[5],_5D[6],_5D[7]];})];}else{var _5E=B(A(_58,[_5v[1],new T(function(){var _5F=E(_5s);return [0,_5F[1],_5F[2],_5F[3],_5g,_5F[5],_5F[6],_5F[7]];}),_])),_5G=_5E,_5H=E(_5G),_5I=E(_5H[1]),_5J=_5I[1];return [0,[0,function(_5K,_){var _5L=B(A(_5u,[_5K,_])),_5M=_5L;if(!E(E(_59)[5])){var _5N=B(_4U(_54,_5J,_5K,_)),_5O=_5N,_5P=B(A(_41,[_4r,_5O,_4q,_5d,_])),_5Q=_5P;return _5K;}else{var _5R=B(A(_5J,[_5K,_])),_5S=_5R;return _5K;}},_5I[2]],_5H[2]];}},_5T=function(_5U,_5V,_){var _5W=jsCreateTextNode(toJSStr(E(_5U))),_5X=_5W,_5Y=jsAppendChild(_5X,E(_5V)[1]);return [0,_5X];},_5Z=new T(function(){return B(unCStr("Prelude.undefined"));}),_60=new T(function(){return B(err(_5Z));}),_61=function(_62,_63){return E(_60);},_64=new T(function(){return B(unCStr(" \u2194 "));}),_65=new T(function(){return B(unCStr(" \u2192 "));}),_66=new T(function(){return B(unCStr(" \u2228 "));}),_67=[0,41],_68=[1,_67,_f],_69=new T(function(){return B(unCStr(" \u2227 "));}),_6a=[0,40],_6b=[0,172],_6c=function(_6d,_6e){switch(E(_6d)[0]){case 0:var _6f=E(_6e);return _6f[0]==0?E(_60):E(_6f[2])[0]==0?[0,_6b,_6f[1]]:E(_60);case 1:var _6g=E(_6e);if(!_6g[0]){return E(_60);}else{var _6h=E(_6g[2]);return _6h[0]==0?E(_60):E(_6h[2])[0]==0?[0,_6a,new T(function(){return B(_1E(_6g[1],new T(function(){return B(_1E(_69,new T(function(){return B(_1E(_6h[1],_68));},1)));},1)));})]:E(_60);}break;case 2:var _6i=E(_6e);if(!_6i[0]){return E(_60);}else{var _6j=E(_6i[2]);return _6j[0]==0?E(_60):E(_6j[2])[0]==0?[0,_6a,new T(function(){return B(_1E(_6i[1],new T(function(){return B(_1E(_66,new T(function(){return B(_1E(_6j[1],_68));},1)));},1)));})]:E(_60);}break;case 3:var _6k=E(_6e);if(!_6k[0]){return E(_60);}else{var _6l=E(_6k[2]);return _6l[0]==0?E(_60):E(_6l[2])[0]==0?[0,_6a,new T(function(){return B(_1E(_6k[1],new T(function(){return B(_1E(_65,new T(function(){return B(_1E(_6l[1],_68));},1)));},1)));})]:E(_60);}break;default:var _6m=E(_6e);if(!_6m[0]){return E(_60);}else{var _6n=E(_6m[2]);return _6n[0]==0?E(_60):E(_6n[2])[0]==0?[0,_6a,new T(function(){return B(_1E(_6m[1],new T(function(){return B(_1E(_64,new T(function(){return B(_1E(_6n[1],_68));},1)));},1)));})]:E(_60);}}},_6o=function(_6p,_6q){var _6r=B(_6c(_6p,_6q));return [1,_6r[1],_6r[2]];},_6s=function(_6t){return new F(function(){return unAppCStr("P_",new T(function(){return B(_4e(0,E(E(_6t)[2])[1],_f));}));});},_6u=function(_6v,_6w){return new F(function(){return _6s(_6v);});},_6x=function(_6y){return E(_60);},_6z=[0,_],_6A=function(_6B){return [1,_,_6B];},_6C=[0,_],_6D=function(_6E){return [1,_,_6E];},_6F=function(_6G){var _6H=E(_6G);switch(_6H[0]){case 0:return E(_6C);case 1:return new F(function(){return _6D(_6H[1]);});break;case 2:return [3,_,_6H[1],new T(function(){return B(_6F(_6H[2]));})];default:return [5,_,_6H[1],new T(function(){return B(_6F(_6H[2]));}),new T(function(){return B(_6F(_6H[3]));})];}},_6I=function(_6J){var _6K=E(_6J);switch(_6K[0]){case 0:return E(_6z);case 1:return new F(function(){return _6A(_6K[1]);});break;case 2:return [3,_,_6K[1],new T(function(){return B(_6F(_6K[2]));})];case 3:return [5,_,_6K[1],new T(function(){return B(_6F(_6K[2]));}),new T(function(){return B(_6F(_6K[3]));})];case 4:return [7,_,_6K[1],new T(function(){return B(_6I(_6K[2]));})];case 5:return [9,_,_6K[1],new T(function(){return B(_6I(_6K[2]));}),new T(function(){return B(_6I(_6K[3]));})];default:return [11,_,_6K[1],function(_6L){return new F(function(){return _6I(B(A(_6K[2],[_6L])));});}];}},_6M=function(_6N){return E(_60);},_6O=function(_6P,_6Q){switch(E(_6P)[0]){case 0:switch(E(_6Q)[0]){case 0:return 1;case 1:return 0;case 2:return 0;default:return 0;}break;case 1:switch(E(_6Q)[0]){case 0:return 2;case 1:return 1;case 2:return 0;default:return 0;}break;case 2:switch(E(_6Q)[0]){case 2:return 1;case 3:return 0;default:return 2;}break;default:return E(_6Q)[0]==3?1:2;}},_6R=new T(function(){return B(unCStr("end of input"));}),_6S=new T(function(){return B(unCStr("unexpected"));}),_6T=new T(function(){return B(unCStr("expecting"));}),_6U=new T(function(){return B(unCStr("unknown parse error"));}),_6V=new T(function(){return B(unCStr("or"));}),_6W=[0,58],_6X=[0,34],_6Y=[0,41],_6Z=[1,_6Y,_f],_70=function(_71,_72,_73){var _74=new T(function(){return B(unAppCStr("(line ",new T(function(){return B(_1E(B(_4e(0,_72,_f)),new T(function(){return B(unAppCStr(", column ",new T(function(){return B(_1E(B(_4e(0,_73,_f)),_6Z));})));},1)));})));}),_75=E(_71);return _75[0]==0?E(_74):[1,_6X,new T(function(){return B(_1E(_75,new T(function(){return B(unAppCStr("\" ",_74));},1)));})];},_76=function(_77,_78){while(1){var _79=E(_77);if(!_79[0]){return E(_78)[0]==0?true:false;}else{var _7a=E(_78);if(!_7a[0]){return false;}else{if(E(_79[1])[1]!=E(_7a[1])[1]){return false;}else{_77=_79[2];_78=_7a[2];continue;}}}}},_7b=function(_7c,_7d){return !B(_76(_7c,_7d))?true:false;},_7e=[0,_76,_7b],_7f=function(_7g,_7h,_7i){var _7j=E(_7i);if(!_7j[0]){return E(_7h);}else{return new F(function(){return _1E(_7h,new T(function(){return B(_1E(_7g,new T(function(){return B(_7f(_7g,_7j[1],_7j[2]));},1)));},1));});}},_7k=function(_7l){return E(_7l)[0]==0?false:true;},_7m=new T(function(){return B(unCStr(", "));}),_7n=function(_7o){var _7p=E(_7o);if(!_7p[0]){return [0];}else{return new F(function(){return _1E(_7p[1],new T(function(){return B(_7n(_7p[2]));},1));});}},_7q=function(_7r,_7s){while(1){var _7t=(function(_7u,_7v){var _7w=E(_7v);if(!_7w[0]){return [0];}else{var _7x=_7w[1],_7y=_7w[2];if(!B(A(_7u,[_7x]))){var _7z=_7u;_7s=_7y;_7r=_7z;return null;}else{return [1,_7x,new T(function(){return B(_7q(_7u,_7y));})];}}})(_7r,_7s);if(_7t!=null){return _7t;}}},_7A=function(_7B,_7C){var _7D=E(_7C);return _7D[0]==0?[0]:[1,_7B,new T(function(){return B(_7A(_7D[1],_7D[2]));})];},_7E=function(_7F,_7G){while(1){var _7H=E(_7G);if(!_7H[0]){return E(_7F);}else{_7F=_7H[1];_7G=_7H[2];continue;}}},_7I=function(_7J){switch(E(_7J)[0]){case 0:return true;case 1:return false;case 2:return false;default:return false;}},_7K=function(_7L){return E(_7L)[0]==1?true:false;},_7M=function(_7N){return E(_7N)[0]==2?true:false;},_7O=[0,10],_7P=[1,_7O,_f],_7Q=function(_7R){return new F(function(){return _1E(_7P,_7R);});},_7S=[0,32],_7T=function(_7U,_7V){var _7W=E(_7V);return _7W[0]==0?[0]:[1,new T(function(){return B(A(_7U,[_7W[1]]));}),new T(function(){return B(_7T(_7U,_7W[2]));})];},_7X=function(_7Y){var _7Z=E(_7Y);switch(_7Z[0]){case 0:return E(_7Z[1]);case 1:return E(_7Z[1]);case 2:return E(_7Z[1]);default:return E(_7Z[1]);}},_80=function(_81){return E(E(_81)[1]);},_82=function(_83,_84,_85){while(1){var _86=E(_85);if(!_86[0]){return false;}else{if(!B(A(_80,[_83,_84,_86[1]]))){_85=_86[2];continue;}else{return true;}}}},_87=function(_88,_89){var _8a=function(_8b,_8c){while(1){var _8d=(function(_8e,_8f){var _8g=E(_8e);if(!_8g[0]){return [0];}else{var _8h=_8g[1],_8i=_8g[2];if(!B(_82(_88,_8h,_8f))){return [1,_8h,new T(function(){return B(_8a(_8i,[1,_8h,_8f]));})];}else{_8b=_8i;var _8j=_8f;_8c=_8j;return null;}}})(_8b,_8c);if(_8d!=null){return _8d;}}};return new F(function(){return _8a(_89,_f);});},_8k=function(_8l,_8m,_8n,_8o,_8p,_8q){var _8r=E(_8q);if(!_8r[0]){return E(_8m);}else{var _8s=new T(function(){var _8t=B(_2b(_7I,_8r));return [0,_8t[1],_8t[2]];}),_8u=new T(function(){var _8v=B(_2b(_7K,E(_8s)[2]));return [0,_8v[1],_8v[2]];}),_8w=new T(function(){return E(E(_8u)[1]);}),_8x=function(_8y,_8z){var _8A=E(_8z);if(!_8A[0]){return E(_8y);}else{var _8B=new T(function(){return B(_1E(_8l,[1,_7S,new T(function(){return B(_7E(_8y,_8A));})]));}),_8C=B(_87(_7e,B(_7q(_7k,B(_7A(_8y,_8A))))));if(!_8C[0]){return new F(function(){return _1E(_f,[1,_7S,_8B]);});}else{var _8D=_8C[1],_8E=E(_8C[2]);if(!_8E[0]){return new F(function(){return _1E(_8D,[1,_7S,_8B]);});}else{return new F(function(){return _1E(B(_1E(_8D,new T(function(){return B(_1E(_7m,new T(function(){return B(_7f(_7m,_8E[1],_8E[2]));},1)));},1))),[1,_7S,_8B]);});}}}},_8F=function(_8G,_8H){var _8I=B(_87(_7e,B(_7q(_7k,B(_7T(_7X,_8H))))));if(!_8I[0]){return [0];}else{var _8J=_8I[1],_8K=_8I[2],_8L=E(_8G);return _8L[0]==0?B(_8x(_8J,_8K)):B(_1E(_8L,[1,_7S,new T(function(){return B(_8x(_8J,_8K));})]));}},_8M=new T(function(){var _8N=B(_2b(_7M,E(_8u)[2]));return [0,_8N[1],_8N[2]];});return new F(function(){return _7n(B(_7T(_7Q,B(_87(_7e,B(_7q(_7k,[1,new T(function(){if(!E(_8w)[0]){var _8O=E(E(_8s)[1]);if(!_8O[0]){var _8P=[0];}else{var _8Q=E(_8O[1]);switch(_8Q[0]){case 0:var _8R=E(_8Q[1]),_8S=_8R[0]==0?B(_1E(_8o,[1,_7S,_8p])):B(_1E(_8o,[1,_7S,_8R]));break;case 1:var _8T=E(_8Q[1]),_8S=_8T[0]==0?B(_1E(_8o,[1,_7S,_8p])):B(_1E(_8o,[1,_7S,_8T]));break;case 2:var _8U=E(_8Q[1]),_8S=_8U[0]==0?B(_1E(_8o,[1,_7S,_8p])):B(_1E(_8o,[1,_7S,_8U]));break;default:var _8V=E(_8Q[1]),_8S=_8V[0]==0?B(_1E(_8o,[1,_7S,_8p])):B(_1E(_8o,[1,_7S,_8V]));}var _8P=_8S;}var _8W=_8P,_8X=_8W;}else{var _8X=[0];}return _8X;}),[1,new T(function(){return B(_8F(_8o,_8w));}),[1,new T(function(){return B(_8F(_8n,E(_8M)[1]));}),[1,new T(function(){return B((function(_8Y){var _8Z=B(_87(_7e,B(_7q(_7k,B(_7T(_7X,_8Y))))));return _8Z[0]==0?[0]:B(_8x(_8Z[1],_8Z[2]));})(E(_8M)[2]));}),_f]]]])))))));});}},_90=[1,_f,_f],_91=function(_92,_93){var _94=function(_95,_96){var _97=E(_95);if(!_97[0]){return E(_96);}else{var _98=_97[1],_99=E(_96);if(!_99[0]){return E(_97);}else{var _9a=_99[1];return B(A(_92,[_98,_9a]))==2?[1,_9a,new T(function(){return B(_94(_97,_99[2]));})]:[1,_98,new T(function(){return B(_94(_97[2],_99));})];}}},_9b=function(_9c){var _9d=E(_9c);if(!_9d[0]){return [0];}else{var _9e=E(_9d[2]);return _9e[0]==0?E(_9d):[1,new T(function(){return B(_94(_9d[1],_9e[1]));}),new T(function(){return B(_9b(_9e[2]));})];}},_9f=function(_9g){while(1){var _9h=E(_9g);if(!_9h[0]){return E(new T(function(){return B(_9f(B(_9b(_f))));}));}else{if(!E(_9h[2])[0]){return E(_9h[1]);}else{_9g=B(_9b(_9h));continue;}}}},_9i=new T(function(){return B(_9j(_f));}),_9j=function(_9k){var _9l=E(_9k);if(!_9l[0]){return E(_90);}else{var _9m=_9l[1],_9n=E(_9l[2]);if(!_9n[0]){return [1,_9l,_f];}else{var _9o=_9n[1],_9p=_9n[2];if(B(A(_92,[_9m,_9o]))==2){return new F(function(){return (function(_9q,_9r,_9s){while(1){var _9t=(function(_9u,_9v,_9w){var _9x=E(_9w);if(!_9x[0]){return [1,[1,_9u,_9v],_9i];}else{var _9y=_9x[1];if(B(A(_92,[_9u,_9y]))==2){_9q=_9y;var _9z=[1,_9u,_9v];_9s=_9x[2];_9r=_9z;return null;}else{return [1,[1,_9u,_9v],new T(function(){return B(_9j(_9x));})];}}})(_9q,_9r,_9s);if(_9t!=null){return _9t;}}})(_9o,[1,_9m,_f],_9p);});}else{return new F(function(){return (function(_9A,_9B,_9C){while(1){var _9D=(function(_9E,_9F,_9G){var _9H=E(_9G);if(!_9H[0]){return [1,new T(function(){return B(A(_9F,[[1,_9E,_f]]));}),_9i];}else{var _9I=_9H[1],_9J=_9H[2];switch(B(A(_92,[_9E,_9I]))){case 0:_9A=_9I;_9B=function(_9K){return new F(function(){return A(_9F,[[1,_9E,_9K]]);});};_9C=_9J;return null;case 1:_9A=_9I;_9B=function(_9L){return new F(function(){return A(_9F,[[1,_9E,_9L]]);});};_9C=_9J;return null;default:return [1,new T(function(){return B(A(_9F,[[1,_9E,_f]]));}),new T(function(){return B(_9j(_9H));})];}}})(_9A,_9B,_9C);if(_9D!=null){return _9D;}}})(_9o,function(_9M){return [1,_9m,_9M];},_9p);});}}}};return new F(function(){return _9f(B(_9j(_93)));});},_9N=function(_9O,_9P,_9Q,_9R){return new F(function(){return _1E(B(_70(_9O,_9P,_9Q)),[1,_6W,new T(function(){return B(_8k(_6V,_6U,_6T,_6S,_6R,B(_91(_6O,_9R))));})]);});},_9S=function(_9T){var _9U=E(_9T),_9V=E(_9U[1]);return new F(function(){return _9N(_9V[1],_9V[2],_9V[3],_9U[2]);});},_9W=function(_9X,_9Y){switch(E(_9X)[0]){case 0:return E(_9Y)[0]==0?true:false;case 1:return E(_9Y)[0]==1?true:false;case 2:return E(_9Y)[0]==2?true:false;case 3:return E(_9Y)[0]==3?true:false;default:return E(_9Y)[0]==4?true:false;}},_9Z=function(_a0,_a1){return E(_a0)[1]==E(_a1)[1];},_a2=function(_a3,_a4){return new F(function(){return _9Z(E(_a3)[2],E(_a4)[2]);});},_a5=function(_a6,_a7){return E(_60);},_a8=new T(function(){return B(unCStr(" . "));}),_a9=function(_aa){var _ab=E(_aa);switch(_ab[0]){case 0:return E(_ab[3]);case 1:return E(_ab[3]);case 2:return E(_ab[3]);case 3:return E(_ab[3]);case 4:return E(_ab[3]);case 5:return E(_ab[3]);case 6:return E(_ab[3]);case 7:return E(_ab[3]);case 8:return E(_ab[3]);default:return E(_ab[3]);}},_ac=[0,41],_ad=[1,_ac,_f],_ae=new T(function(){return B(_2w("AbstractSyntaxMultiUnification.hs:(108,9)-(116,83)|function schematize"));}),_af=[0,44],_ag=[0,40],_ah=function(_ai,_aj,_ak){var _al=E(_ak);switch(_al[0]){case 0:return E(_ae);case 1:return new F(function(){return A(_ai,[_al[2],_f]);});break;case 2:return new F(function(){return _a9(_al[2]);});break;case 3:return new F(function(){return A(_aj,[_al[2],[1,new T(function(){return B(_ah(_ai,_aj,_al[3]));}),_f]]);});break;case 4:return new F(function(){return _1E(B(_a9(_al[2])),[1,_ag,new T(function(){return B(_1E(B(_ah(_ai,_aj,_al[3])),_ad));})]);});break;case 5:return new F(function(){return A(_aj,[_al[2],[1,new T(function(){return B(_ah(_ai,_aj,_al[3]));}),[1,new T(function(){return B(_ah(_ai,_aj,_al[4]));}),_f]]]);});break;default:return new F(function(){return _1E(B(_a9(_al[2])),[1,_ag,new T(function(){return B(_1E(B(_ah(_ai,_aj,_al[3])),[1,_af,new T(function(){return B(_1E(B(_ah(_ai,_aj,_al[4])),_ad));})]));})]);});}},_am=[0],_an=function(_ao,_ap,_aq,_ar,_as,_at,_au,_av){var _aw=E(_av);switch(_aw[0]){case 0:return [0];case 1:return new F(function(){return A(_ar,[_aw[2],_f]);});break;case 2:return new F(function(){return _a9(_aw[2]);});break;case 3:return new F(function(){return A(_ao,[_aw[2],[1,new T(function(){return B(_ah(_ar,_as,_aw[3]));}),_f]]);});break;case 4:return new F(function(){return _1E(B(_a9(_aw[2])),[1,_ag,new T(function(){return B(_1E(B(_ah(_ar,_as,_aw[3])),_ad));})]);});break;case 5:return new F(function(){return A(_ao,[_aw[2],[1,new T(function(){return B(_ah(_ar,_as,_aw[3]));}),[1,new T(function(){return B(_ah(_ar,_as,_aw[4]));}),_f]]]);});break;case 6:return new F(function(){return _1E(B(_a9(_aw[2])),[1,_ag,new T(function(){return B(_1E(B(_ah(_ar,_as,_aw[3])),[1,_af,new T(function(){return B(_1E(B(_ah(_ar,_as,_aw[4])),_ad));})]));})]);});break;case 7:return new F(function(){return A(_ap,[_aw[2],[1,new T(function(){return B(_an(_ao,_ap,_aq,_ar,_as,_at,_au,_aw[3]));}),_f]]);});break;case 8:return new F(function(){return _1E(B(_a9(_aw[2])),new T(function(){return B(_an(_ao,_ap,_aq,_ar,_as,_at,_au,_aw[3]));},1));});break;case 9:return new F(function(){return A(_ap,[_aw[2],[1,new T(function(){return B(_an(_ao,_ap,_aq,_ar,_as,_at,_au,_aw[3]));}),[1,new T(function(){return B(_an(_ao,_ap,_aq,_ar,_as,_at,_au,_aw[4]));}),_f]]]);});break;case 10:return [1,_ag,new T(function(){return B(_1E(B(_an(_ao,_ap,_aq,_ar,_as,_at,_au,_aw[3])),new T(function(){return B(_1E(B(_a9(_aw[2])),new T(function(){return B(_1E(B(_an(_ao,_ap,_aq,_ar,_as,_at,_au,_aw[4])),_ad));},1)));},1)));})];case 11:var _ax=_aw[2],_ay=_aw[3];return new F(function(){return A(_aq,[_ax,[1,new T(function(){return B(A(_at,[new T(function(){return B(A(_ay,[_am]));}),_ax]));}),[1,new T(function(){return B(_an(_ao,_ap,_aq,_ar,_as,_at,_au,B(A(_ay,[_am]))));}),_f]]]);});break;default:var _az=_aw[2],_aA=_aw[3];return new F(function(){return _1E(B(_a9(_az)),new T(function(){return B(_1E(B(A(_au,[new T(function(){return B(A(_aA,[_am]));}),_az])),[1,_ag,new T(function(){return B(_1E(B(_an(_ao,_ap,_aq,_ar,_as,_at,_au,B(A(_aA,[_am])))),_ad));})]));},1));});}},_aB=function(_aC){var _aD=E(_aC);if(!_aD[0]){return [0];}else{return new F(function(){return _1E(_aD[1],new T(function(){return B(_aB(_aD[2]));},1));});}},_aE=function(_aF,_aG){var _aH=E(_aG);return _aH[0]==0?[0]:[1,_aF,[1,_aH[1],new T(function(){return B(_aE(_aF,_aH[2]));})]];},_aI=function(_aJ,_aK,_aL,_aM,_aN,_aO,_aP,_aQ){var _aR=E(_aQ);if(!_aR[0]){return new F(function(){return _a9(_aR[1]);});}else{var _aS=B(_7T(function(_aT){return new F(function(){return _an(_aJ,_aK,_aL,_aN,_aM,_aO,_aP,_aT);});},_aR[1]));return _aS[0]==0?[0]:B(_aB([1,_aS[1],new T(function(){return B(_aE(_a8,_aS[2]));})]));}},_aU=new T(function(){return B(unCStr(" . "));}),_aV=function(_aW){return new F(function(){return _aI(_6x,_6o,_6x,_6x,_6u,_61,_6M,_aW);});},_aX=new T(function(){return B(unCStr(" \u2234 "));}),_aY=function(_aZ,_b0){var _b1=new T(function(){return B(_1E(_aX,new T(function(){return B(_aI(_6x,_6o,_6x,_6x,_6u,_61,_6M,_b0));},1)));},1),_b2=B(_7T(_aV,_aZ));if(!_b2[0]){return E(_b1);}else{return new F(function(){return _1E(B(_aB([1,_b2[1],new T(function(){return B(_aE(_aU,_b2[2]));})])),_b1);});}},_b3=function(_b4,_b5,_b6){while(1){var _b7=E(_b5);if(!_b7[0]){return E(_b6)[0]==0?true:false;}else{var _b8=E(_b6);if(!_b8[0]){return false;}else{if(!B(A(_80,[_b4,_b7[1],_b8[1]]))){return false;}else{_b5=_b7[2];_b6=_b8[2];continue;}}}}},_b9=function(_ba,_bb,_bc){var _bd=E(_bb),_be=E(_bc);return !B(_b3(_ba,_bd[1],_be[1]))?true:!B(A(_80,[_ba,_bd[2],_be[2]]))?true:false;},_bf=function(_bg,_bh,_bi,_bj,_bk){return !B(_b3(_bg,_bh,_bj))?false:B(A(_80,[_bg,_bi,_bk]));},_bl=function(_bm,_bn,_bo){var _bp=E(_bn),_bq=E(_bo);return new F(function(){return _bf(_bm,_bp[1],_bp[2],_bq[1],_bq[2]);});},_br=function(_bs){return [0,function(_bt,_bu){return new F(function(){return _bl(_bs,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _b9(_bs,_bt,_bu);});}];},_bv=function(_bw,_bx){while(1){var _by=E(_bw);if(!_by[0]){return E(_bx)[0]==0?true:false;}else{var _bz=E(_bx);if(!_bz[0]){return false;}else{if(E(_by[1])[1]!=E(_bz[1])[1]){return false;}else{_bw=_by[2];_bx=_bz[2];continue;}}}}},_bA=function(_bB,_bC,_bD,_bE,_bF,_bG,_bH,_bI,_bJ){return new F(function(){return _bv(B(_aI(_bB,_bC,_bD,_bE,_bF,_bG,_bH,_bI)),B(_aI(_bB,_bC,_bD,_bE,_bF,_bG,_bH,_bJ)));});},_bK=function(_bL,_bM,_bN,_bO,_bP,_bQ,_bR,_bS,_bT){return !B(_bA(_bL,_bM,_bN,_bO,_bP,_bQ,_bR,_bS,_bT))?true:false;},_bU=function(_bV,_bW,_bX,_bY,_bZ,_c0,_c1){return [0,function(_c2,_c3){return new F(function(){return _bA(_bV,_bW,_bX,_bY,_bZ,_c0,_c1,_c2,_c3);});},function(_c2,_c3){return new F(function(){return _bK(_bV,_bW,_bX,_bY,_bZ,_c0,_c1,_c2,_c3);});}];},_c4=function(_c5,_c6,_c7){var _c8=E(_c6),_c9=E(_c7);return !B(_b3(_c5,_c8[1],_c9[1]))?true:!B(A(_80,[_c5,_c8[2],_c9[2]]))?true:false;},_ca=function(_cb,_cc,_cd){var _ce=E(_cc),_cf=E(_cd);return new F(function(){return _bf(_cb,_ce[1],_ce[2],_cf[1],_cf[2]);});},_cg=function(_ch){return [0,function(_bt,_bu){return new F(function(){return _ca(_ch,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _c4(_ch,_bt,_bu);});}];},_ci=function(_cj,_ck,_cl){var _cm=E(_cj);switch(_cm[0]){case 0:var _cn=E(_ck);return _cn[0]==0?!B(_bv(_cm[3],_cn[3]))?[0]:[1,_cl]:[0];case 1:var _co=E(_ck);return _co[0]==1?!B(_bv(_cm[3],_co[3]))?[0]:[1,_cl]:[0];case 2:var _cp=E(_ck);return _cp[0]==2?!B(_bv(_cm[3],_cp[3]))?[0]:[1,_cl]:[0];case 3:var _cq=E(_ck);return _cq[0]==3?!B(_bv(_cm[3],_cq[3]))?[0]:[1,_cl]:[0];case 4:var _cr=E(_ck);return _cr[0]==4?!B(_bv(_cm[3],_cr[3]))?[0]:[1,_cl]:[0];case 5:var _cs=E(_ck);return _cs[0]==5?!B(_bv(_cm[3],_cs[3]))?[0]:[1,_cl]:[0];case 6:var _ct=E(_ck);return _ct[0]==6?!B(_bv(_cm[3],_ct[3]))?[0]:[1,_cl]:[0];case 7:var _cu=E(_ck);return _cu[0]==7?!B(_bv(_cm[3],_cu[3]))?[0]:[1,_cl]:[0];case 8:var _cv=E(_ck);return _cv[0]==8?!B(_bv(_cm[3],_cv[3]))?[0]:[1,_cl]:[0];default:var _cw=E(_ck);return _cw[0]==9?!B(_bv(_cm[3],_cw[3]))?[0]:[1,_cl]:[0];}},_cx=new T(function(){return B(_2w("AbstractDerivationMultiUnification.hs:(45,37)-(47,31)|case"));}),_cy=function(_cz,_cA){return [3,_,_cz,_cA];},_cB=function(_cC,_cD,_cE){while(1){var _cF=E(_cE);if(!_cF[0]){return [0];}else{var _cG=E(_cF[1]),_cH=B(A(_cC,[_cD,_cG[2],_cG[3]]));if(!_cH[0]){_cE=_cF[2];continue;}else{return E(_cH);}}}},_cI=function(_cJ,_cK){while(1){var _cL=(function(_cM,_cN){var _cO=E(_cN);switch(_cO[0]){case 2:var _cP=B(_cB(_ci,_cO[2],_cM));if(!_cP[0]){return E(_cO);}else{var _cQ=_cM;_cK=_cP[1];_cJ=_cQ;return null;}break;case 4:var _cR=_cO[3],_cS=B(_cB(_ci,_cO[2],_cM));if(!_cS[0]){return E(_cO);}else{var _cT=E(_cS[1]);switch(_cT[0]){case 3:return E(_cT[3])[0]==0?B(_cy(_cT[2],_cR)):E(_cO);case 4:if(!E(_cT[3])[0]){var _cQ=_cM;_cK=[4,_,_cT[2],_cR];_cJ=_cQ;return null;}else{return E(_cO);}break;default:return E(_cO);}}break;case 6:var _cU=_cO[3],_cV=_cO[4],_cW=B(_cB(_ci,_cO[2],_cM));if(!_cW[0]){return E(_cO);}else{var _cX=E(_cW[1]);switch(_cX[0]){case 5:if(!E(_cX[3])[0]){if(!E(_cX[4])[0]){var _cQ=_cM;_cK=[5,_,_cX[2],_cU,_cV];_cJ=_cQ;return null;}else{return E(_cO);}}else{return E(_cO);}break;case 6:if(!E(_cX[3])[0]){if(!E(_cX[4])[0]){var _cQ=_cM;_cK=[6,_,_cX[2],_cU,_cV];_cJ=_cQ;return null;}else{return E(_cO);}}else{return E(_cO);}break;default:return E(_cO);}}break;case 7:return [7,_,_cO[2],new T(function(){return B(_cI(_cM,_cO[3]));})];case 8:var _cY=_cO[2],_cZ=_cO[3],_d0=B(_cB(_ci,_cY,_cM));if(!_d0[0]){return [8,_,_cY,new T(function(){return B(_cI(_cM,_cZ));})];}else{var _d1=E(_d0[1]);switch(_d1[0]){case 7:return E(_d1[3])[0]==0?[7,_,_d1[2],new T(function(){return B(_cI(_cM,_cZ));})]:[8,_,_cY,new T(function(){return B(_cI(_cM,_cZ));})];case 8:if(!E(_d1[3])[0]){var _cQ=_cM;_cK=[8,_,_d1[2],_cZ];_cJ=_cQ;return null;}else{return [8,_,_cY,new T(function(){return B(_cI(_cM,_cZ));})];}break;default:return [8,_,_cY,new T(function(){return B(_cI(_cM,_cZ));})];}}break;case 9:return [9,_,_cO[2],new T(function(){return B(_cI(_cM,_cO[3]));}),new T(function(){return B(_cI(_cM,_cO[4]));})];case 10:var _d2=_cO[2],_d3=_cO[3],_d4=_cO[4],_d5=B(_cB(_ci,_d2,_cM));if(!_d5[0]){return [10,_,_d2,new T(function(){return B(_cI(_cM,_d3));}),new T(function(){return B(_cI(_cM,_d4));})];}else{var _d6=E(_d5[1]);switch(_d6[0]){case 9:return E(_d6[3])[0]==0?E(_d6[4])[0]==0?[9,_,_d6[2],new T(function(){return B(_cI(_cM,B(_cI(_cM,_d3))));}),new T(function(){return B(_cI(_cM,B(_cI(_cM,_d4))));})]:[10,_,_d2,new T(function(){return B(_cI(_cM,_d3));}),new T(function(){return B(_cI(_cM,_d4));})]:[10,_,_d2,new T(function(){return B(_cI(_cM,_d3));}),new T(function(){return B(_cI(_cM,_d4));})];case 10:if(!E(_d6[3])[0]){if(!E(_d6[4])[0]){var _cQ=_cM;_cK=[10,_,_d6[2],_d3,_d4];_cJ=_cQ;return null;}else{return [10,_,_d2,new T(function(){return B(_cI(_cM,_d3));}),new T(function(){return B(_cI(_cM,_d4));})];}}else{return [10,_,_d2,new T(function(){return B(_cI(_cM,_d3));}),new T(function(){return B(_cI(_cM,_d4));})];}break;default:return [10,_,_d2,new T(function(){return B(_cI(_cM,_d3));}),new T(function(){return B(_cI(_cM,_d4));})];}}break;case 11:return [11,_,_cO[2],function(_d7){return new F(function(){return _cI(_cM,B(A(_cO[3],[_d7])));});}];case 12:var _d8=_cO[2],_d9=_cO[3],_da=B(_cB(_ci,_d8,_cM));if(!_da[0]){return [12,_,_d8,function(_db){return new F(function(){return _cI(_cM,B(A(_d9,[_db])));});}];}else{var _dc=E(_da[1]);switch(_dc[0]){case 11:return [11,_,_dc[2],function(_dd){return new F(function(){return _cI(_cM,B(A(_d9,[_dd])));});}];case 12:var _cQ=_cM;_cK=[12,_,_dc[2],_d9];_cJ=_cQ;return null;default:return [12,_,_d8,function(_de){return new F(function(){return _cI(_cM,B(A(_d9,[_de])));});}];}}break;default:return E(_cO);}})(_cJ,_cK);if(_cL!=null){return _cL;}}},_df=function(_dg,_dh){var _di=E(_dh);if(!_di[0]){var _dj=B(_cB(_ci,_di[1],_dg));if(!_dj[0]){return E(_di);}else{var _dk=E(_dj[1]);return _dk[0]==0?E(_cx):[1,new T(function(){return B(_7T(function(_dl){return new F(function(){return _cI(_dg,_dl);});},_dk[1]));})];}}else{return [1,new T(function(){return B(_7T(function(_dm){return new F(function(){return _cI(_dg,_dm);});},_di[1]));})];}},_dn=function(_do,_dp,_dq,_dr,_ds,_dt,_du,_dv,_dw){var _dx=E(_dw);return [0,new T(function(){return B(_7T(function(_dy){return new F(function(){return _df(_dv,_dy);});},_dx[1]));}),new T(function(){return B(_df(_dv,_dx[2]));})];},_dz=function(_dA,_dB,_dC,_dD,_dE,_dF,_dG,_dH,_dI){var _dJ=E(_dI);return [0,new T(function(){return B(_7T(function(_dK){return new F(function(){return _dn(_dA,_dB,_dC,_dD,_dE,_dF,_dG,_dH,_dK);});},_dJ[1]));}),new T(function(){return B(_dn(_dA,_dB,_dC,_dD,_dE,_dF,_dG,_dH,_dJ[2]));})];},_dL=function(_dM){return E(E(_dM)[1]);},_dN=function(_dO,_dP){var _dQ=E(_dP);return new F(function(){return A(_dL,[_dQ[1],E(_dO)[2],_dQ[2]]);});},_dR=function(_dS,_dT,_dU){var _dV=E(_dU);if(!_dV[0]){return [0];}else{var _dW=_dV[1],_dX=_dV[2];return !B(A(_dS,[_dT,_dW]))?[1,_dW,new T(function(){return B(_dR(_dS,_dT,_dX));})]:E(_dX);}},_dY=function(_dZ,_e0,_e1){while(1){var _e2=E(_e1);if(!_e2[0]){return false;}else{if(!B(A(_dZ,[_e0,_e2[1]]))){_e1=_e2[2];continue;}else{return true;}}}},_e3=function(_e4,_e5){var _e6=function(_e7,_e8){while(1){var _e9=(function(_ea,_eb){var _ec=E(_ea);if(!_ec[0]){return [0];}else{var _ed=_ec[1],_ee=_ec[2];if(!B(_dY(_e4,_ed,_eb))){return [1,_ed,new T(function(){return B(_e6(_ee,[1,_ed,_eb]));})];}else{_e7=_ee;var _ef=_eb;_e8=_ef;return null;}}})(_e7,_e8);if(_e9!=null){return _e9;}}};return new F(function(){return _e6(_e5,_f);});},_eg=function(_eh,_ei,_ej){return new F(function(){return _1E(_ei,new T(function(){return B((function(_ek,_el){while(1){var _em=E(_el);if(!_em[0]){return E(_ek);}else{var _en=B(_dR(_eh,_em[1],_ek));_el=_em[2];_ek=_en;continue;}}})(B(_e3(_eh,_ej)),_ei));},1));});},_eo=function(_ep,_eq){while(1){var _er=(function(_es,_et){var _eu=E(_et);switch(_eu[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_es,_eu[2]],_f];case 3:var _ev=_es;_eq=_eu[3];_ep=_ev;return null;case 4:return new F(function(){return _eg(_dN,[1,[0,_es,_eu[2]],_f],new T(function(){return B(_eo(_es,_eu[3]));},1));});break;case 5:return new F(function(){return _eg(_dN,B(_eo(_es,_eu[3])),new T(function(){return B(_eo(_es,_eu[4]));},1));});break;default:return new F(function(){return _eg(_dN,B(_eg(_dN,[1,[0,_es,_eu[2]],_f],new T(function(){return B(_eo(_es,_eu[3]));},1))),new T(function(){return B(_eo(_es,_eu[4]));},1));});}})(_ep,_eq);if(_er!=null){return _er;}}},_ew=function(_ex,_ey,_ez,_eA){while(1){var _eB=(function(_eC,_eD,_eE,_eF){var _eG=E(_eF);switch(_eG[0]){case 0:return [0];case 1:return [0];case 2:return [1,[0,_eC,_eG[2]],_f];case 3:return new F(function(){return _eo(_eC,_eG[3]);});break;case 4:return new F(function(){return _eg(_dN,[1,[0,_eC,_eG[2]],_f],new T(function(){return B(_eo(_eC,_eG[3]));},1));});break;case 5:return new F(function(){return _eg(_dN,B(_eo(_eC,_eG[3])),new T(function(){return B(_eo(_eC,_eG[4]));},1));});break;case 6:return new F(function(){return _eg(_dN,B(_eg(_dN,[1,[0,_eC,_eG[2]],_f],new T(function(){return B(_eo(_eC,_eG[3]));},1))),new T(function(){return B(_eo(_eC,_eG[4]));},1));});break;case 7:var _eH=_eC,_eI=_eD,_eJ=_eE;_eA=_eG[3];_ex=_eH;_ey=_eI;_ez=_eJ;return null;case 8:return new F(function(){return _eg(_dN,[1,[0,_eC,_eG[2]],_f],new T(function(){return B(_ew(_eC,_eD,_eE,_eG[3]));},1));});break;case 9:return new F(function(){return _eg(_dN,B(_ew(_eC,_eD,_eE,_eG[3])),new T(function(){return B(_ew(_eC,_eD,_eE,_eG[4]));},1));});break;case 10:return new F(function(){return _eg(_dN,B(_eg(_dN,[1,[0,_eC,_eG[2]],_f],new T(function(){return B(_ew(_eC,_eD,_eE,_eG[3]));},1))),new T(function(){return B(_ew(_eC,_eD,_eE,_eG[4]));},1));});break;case 11:var _eH=_eC,_eI=_eD,_eJ=_eE;_eA=B(A(_eG[3],[_am]));_ex=_eH;_ey=_eI;_ez=_eJ;return null;default:return new F(function(){return _eg(_dN,[1,[0,_eC,_eG[2]],_f],new T(function(){return B(_ew(_eC,_eD,_eE,B(A(_eG[3],[_am]))));},1));});}})(_ex,_ey,_ez,_eA);if(_eB!=null){return _eB;}}},_eK=function(_eL,_eM,_eN,_eO,_eP){var _eQ=function(_eR){return new F(function(){return _ew(_eL,_eM,_eN,_eR);});};return new F(function(){return _1E(B(_7n(B(_7T(function(_eS){var _eT=E(_eS);if(!_eT[0]){return [1,[0,_eL,_eT[1]],_f];}else{return new F(function(){return _7n(B(_7T(_eQ,_eT[1])));});}},_eO)))),new T(function(){var _eU=E(_eP);if(!_eU[0]){var _eV=[1,[0,_eL,_eU[1]],_f];}else{var _eV=B(_7n(B(_7T(_eQ,_eU[1]))));}return _eV;},1));});},_eW=function(_eX,_eY,_eZ,_f0,_f1,_f2,_f3,_f4,_f5){var _f6=E(_f5);return new F(function(){return _1E(B(_7n(B(_7T(function(_f7){var _f8=E(_f7);return new F(function(){return _eK(_eX,_f1,_f2,_f8[1],_f8[2]);});},_f6[1])))),new T(function(){var _f9=E(_f6[2]);return B(_eK(_eX,_f1,_f2,_f9[1],_f9[2]));},1));});},_fa=function(_fb,_fc,_fd,_fe,_ff,_fg,_fh,_fi,_fj,_fk,_fl){return [0,_fb,_fc,_fd,_fe,function(_dK){return new F(function(){return _eW(_fb,_ff,_fg,_fh,_fi,_fj,_fk,_fl,_dK);});},function(_fm,_dK){return new F(function(){return _dz(_ff,_fg,_fh,_fi,_fj,_fk,_fl,_fm,_dK);});}];},_fn=function(_fo){return E(E(_fo)[2]);},_fp=function(_fq){return E(E(_fq)[1]);},_fr=[0,_fp,_fn],_fs=[0,125],_ft=new T(function(){return B(unCStr("given = "));}),_fu=new T(function(){return B(unCStr(", "));}),_fv=new T(function(){return B(unCStr("needed = "));}),_fw=new T(function(){return B(unCStr("AbsRule {"));}),_fx=[0,0],_fy=function(_fz){return E(E(_fz)[3]);},_fA=function(_fB){return E(E(_fB)[1]);},_fC=function(_fD,_fE,_fF,_fG){var _fH=function(_fI){return new F(function(){return _1E(_fw,new T(function(){return B(_1E(_fv,new T(function(){return B(A(new T(function(){return B(A(_fy,[_fD,_fF]));}),[new T(function(){return B(_1E(_fu,new T(function(){return B(_1E(_ft,new T(function(){return B(A(new T(function(){return B(A(_fA,[_fD,_fx,_fG]));}),[[1,_fs,_fI]]));},1)));},1)));})]));},1)));},1));});};return _fE<11?E(_fH):function(_fJ){return [1,_4d,new T(function(){return B(_fH([1,_4c,_fJ]));})];};},_fK=function(_fL,_fM){var _fN=E(_fM);return new F(function(){return A(_fC,[_fL,0,_fN[1],_fN[2],_f]);});},_fO=function(_fP,_fQ,_fR){return new F(function(){return _1O(function(_fS){var _fT=E(_fS);return new F(function(){return _fC(_fP,0,_fT[1],_fT[2]);});},_fQ,_fR);});},_fU=function(_fV,_fW,_fX){var _fY=E(_fX);return new F(function(){return _fC(_fV,E(_fW)[1],_fY[1],_fY[2]);});},_fZ=function(_g0){return [0,function(_bt,_bu){return new F(function(){return _fU(_g0,_bt,_bu);});},function(_bu){return new F(function(){return _fK(_g0,_bu);});},function(_bt,_bu){return new F(function(){return _fO(_g0,_bt,_bu);});}];},_g1=function(_g2,_g3,_g4,_g5,_g6,_g7,_g8,_g9,_ga){return new F(function(){return _1O(function(_gb,_gc){return new F(function(){return _1E(B(_aI(_g2,_g3,_g4,_g5,_g6,_g7,_g8,_gb)),_gc);});},_g9,_ga);});},_gd=function(_ge,_gf,_gg,_gh,_gi,_gj,_gk,_gl,_gm,_gn){return new F(function(){return _1E(B(_aI(_ge,_gf,_gg,_gh,_gi,_gj,_gk,_gm)),_gn);});},_go=function(_gp,_gq,_gr,_gs,_gt,_gu,_gv){return [0,function(_gw,_c2,_c3){return new F(function(){return _gd(_gp,_gq,_gr,_gs,_gt,_gu,_gv,_gw,_c2,_c3);});},function(_c3){return new F(function(){return _aI(_gp,_gq,_gr,_gs,_gt,_gu,_gv,_c3);});},function(_c2,_c3){return new F(function(){return _g1(_gp,_gq,_gr,_gs,_gt,_gu,_gv,_c2,_c3);});}];},_gx=new T(function(){return B(unCStr("Sequent "));}),_gy=[0,11],_gz=[0,32],_gA=function(_gB,_gC,_gD,_gE){var _gF=new T(function(){return B(A(_fA,[_gB,_gy,_gE]));}),_gG=new T(function(){return B(A(_fy,[_gB,_gD]));});return _gC<11?function(_gH){return new F(function(){return _1E(_gx,new T(function(){return B(A(_gG,[[1,_gz,new T(function(){return B(A(_gF,[_gH]));})]]));},1));});}:function(_gI){return [1,_4d,new T(function(){return B(_1E(_gx,new T(function(){return B(A(_gG,[[1,_gz,new T(function(){return B(A(_gF,[[1,_4c,_gI]]));})]]));},1)));})];};},_gJ=function(_gK,_gL){var _gM=E(_gL);return new F(function(){return A(_gA,[_gK,0,_gM[1],_gM[2],_f]);});},_gN=function(_gO,_gP,_gQ){return new F(function(){return _1O(function(_gR){var _gS=E(_gR);return new F(function(){return _gA(_gO,0,_gS[1],_gS[2]);});},_gP,_gQ);});},_gT=function(_gU,_gV,_gW){var _gX=E(_gW);return new F(function(){return _gA(_gU,E(_gV)[1],_gX[1],_gX[2]);});},_gY=function(_gZ){return [0,function(_bt,_bu){return new F(function(){return _gT(_gZ,_bt,_bu);});},function(_bu){return new F(function(){return _gJ(_gZ,_bu);});},function(_bt,_bu){return new F(function(){return _gN(_gZ,_bt,_bu);});}];},_h0=function(_h1,_h2){return new F(function(){return _1E(B(_a9(_h1)),_h2);});},_h3=function(_h4,_h5){return new F(function(){return _1O(_h0,_h4,_h5);});},_h6=function(_h7,_h8,_h9){return new F(function(){return _1E(B(_a9(_h8)),_h9);});},_ha=[0,_h6,_a9,_h3],_hb=function(_hc,_hd,_he,_hf,_hg,_hh,_hi,_hj,_hk,_hl,_hm,_hn){var _ho=E(_hn);return new F(function(){return _eK(_hc,_hj,_hk,_ho[1],_ho[2]);});},_hp=function(_hq,_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy,_hz,_hA){return [0,_hq,_hr,_hs,_ht,function(_dK){return new F(function(){return _hb(_hq,_hr,_hs,_ht,_hu,_hv,_hw,_hx,_hy,_hz,_hA,_dK);});},function(_fm,_dK){return new F(function(){return _dn(_hu,_hv,_hw,_hx,_hy,_hz,_hA,_fm,_dK);});}];},_hB=function(_hC,_hD){return [0];},_hE=function(_hF,_hG,_hH,_hI,_hJ,_hK,_hL,_hM,_hN,_hO,_hP,_hQ,_hR,_hS){return [0,_hF,_hG,_hB,_60];},_hT=function(_hU,_hV,_hW,_hX,_hY,_hZ,_i0,_i1,_i2,_i3,_i4,_i5){var _i6=E(_i5);if(!_i6[0]){return [1,[0,_hU,_i6[1]],_f];}else{return new F(function(){return _7n(B(_7T(function(_i7){return new F(function(){return _ew(_hU,_i1,_i2,_i7);});},_i6[1])));});}},_i8=function(_i9,_ia,_ib,_ic,_id,_ie,_if,_ig,_ih,_ii,_ij){return [0,_i9,_ia,_ib,_ic,function(_dK){return new F(function(){return _hT(_i9,_ia,_ib,_ic,_id,_ie,_if,_ig,_ih,_ii,_ij,_dK);});},_df];},_ik=function(_il){return new F(function(){return err(B(unAppCStr("Oops!  Entered absent arg ",new T(function(){return B(unCStr(_il));}))));});},_im=new T(function(){return B(_ik("w_sogm{v} [lid] main:AbstractSyntaxMultiUnification.S_NextVar{tc rHY}\n                  sv{tv anUp} [tv] quant{tv anUn} [tv]"));}),_in=new T(function(){return B(_ik("w_sogl{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv anUn} [tv]"));}),_io=new T(function(){return B(_ik("w_sogk{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv anUm} [tv]"));}),_ip=new T(function(){return B(_ik("w_sogj{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv anUp} [tv]"));}),_iq=new T(function(){return B(_ik("w_sogi{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv anUl} [tv]"));}),_ir=new T(function(){return B(_ik("w_sogh{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv anUo} [tv]"));}),_is=new T(function(){return B(_ik("w_sogn{v} [lid] main:AbstractSyntaxMultiUnification.SchemeVar{tc rH8}\n                  sv{tv anUp} [tv]"));}),_it=new T(function(){return B(_ik("w_sogg{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv anUn} [tv]"));}),_iu=new T(function(){return B(_ik("w_sogf{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv anUm} [tv]"));}),_iv=new T(function(){return B(_ik("w_soge{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv anUp} [tv]"));}),_iw=new T(function(){return B(_ik("w_sogd{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv anUl} [tv]"));}),_ix=new T(function(){return B(_ik("w_sogc{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv anUo} [tv]"));}),_iy=function(_iz,_iA){return function(_iB,_iC){var _iD=E(_iB);return _iD[0]==0?[1,[0,new T(function(){return B(_iE(_iz,_iA,_ix,_iw,_iv,_iu,_it,_ir,_iq,_ip,_io,_in,_im,_is));}),_iD[1],_iC]]:[0];};},_iF=function(_iG){return [0,E(_iG)];},_iE=function(_iH,_iI,_iJ,_iK,_iL,_iM,_iN,_iO,_iP,_iQ,_iR,_iS,_iT,_iU){return [0,_iH,_iI,new T(function(){return B(_iy(_iH,_iI));}),_iF];},_iV=[1,_f],_iW=function(_iX,_iY){while(1){var _iZ=E(_iX);if(!_iZ[0]){return E(_iY);}else{_iX=_iZ[2];var _j0=_iY+1|0;_iY=_j0;continue;}}},_j1=[0,95],_j2=[1,_j1,_f],_j3=[1,_j2,_f],_j4=function(_j5,_j6,_j7){return !B(_bv(B(A(_j5,[_j6,_j3])),B(A(_j5,[_j7,_j3]))))?true:false;},_j8=function(_j9){return [0,function(_ja,_jb){return new F(function(){return _bv(B(A(_j9,[_ja,_j3])),B(A(_j9,[_jb,_j3])));});},function(_c2,_c3){return new F(function(){return _j4(_j9,_c2,_c3);});}];},_jc=function(_jd,_je){return new F(function(){return _cI(_jd,_je);});},_jf=function(_jg,_jh,_ji,_jj,_jk,_jl,_jm,_jn,_jo,_jp,_jq){return [0,_jg,_jh,_ji,_jj,function(_jr){return new F(function(){return _ew(_jg,_jn,_jo,_jr);});},_jc];},_js=new T(function(){return B(_ik("w_sk9h{v} [lid] main:AbstractSyntaxMultiUnification.S_NextVar{tc rHY}\n                  sv{tv ah7I} [tv] quant{tv ah7G} [tv]"));}),_jt=new T(function(){return B(_ik("w_sk9g{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  quant{tv ah7G} [tv]"));}),_ju=new T(function(){return B(_ik("w_sk9f{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  con{tv ah7F} [tv]"));}),_jv=new T(function(){return B(_ik("w_sk9e{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  sv{tv ah7I} [tv]"));}),_jw=new T(function(){return B(_ik("w_sk9d{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  pred{tv ah7E} [tv]"));}),_jx=new T(function(){return B(_ik("w_sk9c{v} [lid] main:AbstractSyntaxDataTypes.Schematizable{tc rAk}\n                  f{tv ah7H} [tv]"));}),_jy=new T(function(){return B(_ik("w_sk9i{v} [lid] main:AbstractSyntaxMultiUnification.SchemeVar{tc rH8}\n                  sv{tv ah7I} [tv]"));}),_jz=new T(function(){return B(_ik("w_sk9b{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ah7G} [tv]"));}),_jA=new T(function(){return B(_ik("w_sk9a{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  con{tv ah7F} [tv]"));}),_jB=new T(function(){return B(_ik("w_sk99{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  sv{tv ah7I} [tv]"));}),_jC=new T(function(){return B(_ik("w_sk98{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  pred{tv ah7E} [tv]"));}),_jD=new T(function(){return B(_ik("w_sk97{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ah7H} [tv]"));}),_jE=function(_jF,_jG,_jH,_jI){var _jJ=E(_jH);switch(_jJ[0]){case 2:return [1,[0,new T(function(){return B(_jK(_jF,_jG,_jD,_jC,_jB,_jA,_jz,_jx,_jw,_jv,_ju,_jt,_js,_jy));}),_jJ[2],_jI]];case 4:var _jL=_jJ[2];if(!E(_jJ[3])[0]){var _jM=E(_jI);switch(_jM[0]){case 3:return E(_jM[3])[0]==0?[1,[0,new T(function(){return B(_jK(_jF,_jG,_jD,_jC,_jB,_jA,_jz,_jx,_jw,_jv,_ju,_jt,_js,_jy));}),_jL,_jM]]:[0];case 4:return E(_jM[3])[0]==0?[1,[0,new T(function(){return B(_jK(_jF,_jG,_jD,_jC,_jB,_jA,_jz,_jx,_jw,_jv,_ju,_jt,_js,_jy));}),_jL,_jM]]:[0];default:return [0];}}else{return [0];}break;case 6:var _jN=_jJ[2];if(!E(_jJ[3])[0]){if(!E(_jJ[4])[0]){var _jO=E(_jI);switch(_jO[0]){case 5:return E(_jO[3])[0]==0?E(_jO[4])[0]==0?[1,[0,new T(function(){return B(_jK(_jF,_jG,_jD,_jC,_jB,_jA,_jz,_jx,_jw,_jv,_ju,_jt,_js,_jy));}),_jN,_jO]]:[0]:[0];case 6:return E(_jO[3])[0]==0?E(_jO[4])[0]==0?[1,[0,new T(function(){return B(_jK(_jF,_jG,_jD,_jC,_jB,_jA,_jz,_jx,_jw,_jv,_ju,_jt,_js,_jy));}),_jN,_jO]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;case 8:var _jP=_jJ[2];if(!E(_jJ[3])[0]){var _jQ=E(_jI);switch(_jQ[0]){case 7:return E(_jQ[3])[0]==0?[1,[0,new T(function(){return B(_jK(_jF,_jG,_jD,_jC,_jB,_jA,_jz,_jx,_jw,_jv,_ju,_jt,_js,_jy));}),_jP,_jQ]]:[0];case 8:return E(_jQ[3])[0]==0?[1,[0,new T(function(){return B(_jK(_jF,_jG,_jD,_jC,_jB,_jA,_jz,_jx,_jw,_jv,_ju,_jt,_js,_jy));}),_jP,_jQ]]:[0];default:return [0];}}else{return [0];}break;case 10:var _jR=_jJ[2];if(!E(_jJ[3])[0]){if(!E(_jJ[4])[0]){var _jS=E(_jI);switch(_jS[0]){case 9:return E(_jS[3])[0]==0?E(_jS[4])[0]==0?[1,[0,new T(function(){return B(_jK(_jF,_jG,_jD,_jC,_jB,_jA,_jz,_jx,_jw,_jv,_ju,_jt,_js,_jy));}),_jR,_jS]]:[0]:[0];case 10:return E(_jS[3])[0]==0?E(_jS[4])[0]==0?[1,[0,new T(function(){return B(_jK(_jF,_jG,_jD,_jC,_jB,_jA,_jz,_jx,_jw,_jv,_ju,_jt,_js,_jy));}),_jR,_jS]]:[0]:[0];default:return [0];}}else{return [0];}}else{return [0];}break;default:return [0];}},_jT=new T(function(){return B(_2w("AbstractSyntaxMultiUnification.hs:(443,9)-(447,97)|function multiMakeTerm"));}),_jU=function(_jV){var _jW=E(_jV);switch(_jW[0]){case 3:return [2,_,_jW];case 4:return [4,_,_jW,_6C];case 5:return [6,_,_jW,_6C,_6C];case 6:return [8,_,_jW,_6z];case 7:return [10,_,_jW,_6z,_6z];default:return E(_jT);}},_jK=function(_jX,_jY,_jZ,_k0,_k1,_k2,_k3,_k4,_k5,_k6,_k7,_k8,_k9,_ka){return [0,_jX,_jY,function(_kb,_kc){return new F(function(){return _jE(_jX,_jY,_kb,_kc);});},_jU];},_kd=function(_ke,_kf,_kg){return new F(function(){return _1O(function(_kh,_ki){return new F(function(){return _1E(B(A(_ke,[_kh,_j3])),_ki);});},_kf,_kg);});},_kj=function(_kk){return [0,function(_kl,_km,_kn){return new F(function(){return _1E(B(A(_kk,[_km,_j3])),_kn);});},function(_ko){return new F(function(){return A(_kk,[_ko,_j3]);});},function(_c2,_c3){return new F(function(){return _kd(_kk,_c2,_c3);});}];},_kp=[1,_f],_kq=function(_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_kB,_kC){var _kD=E(_kB);if(_kD[0]==2){return E(_kp);}else{var _kE=E(_kC);if(_kE[0]==2){return E(_kp);}else{var _kF=function(_kG){var _kH=function(_kI){var _kJ=function(_kK){var _kL=function(_kM){var _kN=function(_kO){var _kP=function(_kQ){var _kR=function(_kS){var _kT=function(_kU){var _kV=function(_kW){var _kX=function(_kY){var _kZ=function(_l0){var _l1=function(_l2){var _l3=E(_kD);switch(_l3[0]){case 1:var _l4=E(_kE);return _l4[0]==1?!B(A(_ks,[_l3[2],_l4[2]]))?[0]:E(_kp):[0];case 3:var _l5=E(_kE);return _l5[0]==3?!B(A(_kr,[_l3[2],_l5[2]]))?[0]:E(_kp):[0];case 4:var _l6=_l3[2],_l7=E(_kE);switch(_l7[0]){case 3:return [1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,[4,_,_l6,_6C],[3,_,_l7[2],_6C]]));}),_f]];case 4:return [1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,[4,_,_l6,_6C],[4,_,_l7[2],_6C]]));}),_f]];default:return [0];}break;case 5:var _l9=E(_kE);return _l9[0]==5?!B(A(_kr,[_l3[2],_l9[2]]))?[0]:E(_kp):[0];case 6:var _la=_l3[2],_lb=E(_kE);switch(_lb[0]){case 5:return [1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,[6,_,_la,_6C,_6C],[5,_,_lb[2],_6C,_6C]]));}),_f]];case 6:return [1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,[6,_,_la,_6C,_6C],[6,_,_lb[2],_6C,_6C]]));}),_f]];default:return [0];}break;case 7:var _lc=E(_kE);return _lc[0]==7?!B(A(_kt,[_l3[2],_lc[2]]))?[0]:[1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_l3[3],_lc[3]]));}),_f]]:[0];case 8:var _ld=_l3[2],_le=_l3[3],_lf=E(_kE);switch(_lf[0]){case 7:return [1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,[8,_,_ld,_6z],[7,_,_lf[2],_6z]]));}),[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_le,_lf[3]]));}),_f]]];case 8:return [1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,[8,_,_ld,_6z],[8,_,_lf[2],_6z]]));}),[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_le,_lf[3]]));}),_f]]];default:return [0];}break;case 9:var _lg=E(_kE);return _lg[0]==9?!B(A(_kt,[_l3[2],_lg[2]]))?[0]:[1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_l3[3],_lg[3]]));}),[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_l3[4],_lg[4]]));}),_f]]]:[0];case 10:var _lh=_l3[2],_li=_l3[3],_lj=_l3[4],_lk=function(_ll){var _lm=E(_kE);switch(_lm[0]){case 9:return [1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,[10,_,_lh,_6z,_6z],[9,_,_lm[2],_6z,_6z]]));}),[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_li,_lm[3]]));}),[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_lj,_lm[4]]));}),_f]]]];case 10:return [1,[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,[10,_,_lh,_6z,_6z],[10,_,_lm[2],_6z,_6z]]));}),[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_li,_lm[3]]));}),[1,new T(function(){return B(A(_l8,[_kr,_ks,_kt,_ku,_kv,_kw,_kx,_ky,_kz,_kA,_lj,_lm[4]]));}),_f]]]];default:return [0];}};return E(_li)[0]==0?E(_lj)[0]==0?E(_kp):B(_lk(_)):B(_lk(_));default:return [0];}},_ln=E(_kE);return _ln[0]==10?E(_ln[3])[0]==0?E(_ln[4])[0]==0?E(_kp):B(_l1(_)):B(_l1(_)):B(_l1(_));},_lo=E(_kD);return _lo[0]==8?E(_lo[3])[0]==0?E(_kp):B(_kZ(_)):B(_kZ(_));},_lp=E(_kE);switch(_lp[0]){case 6:return E(_lp[3])[0]==0?E(_lp[4])[0]==0?E(_kp):B(_kX(_)):B(_kX(_));case 8:return E(_lp[3])[0]==0?E(_kp):B(_kX(_));default:return new F(function(){return _kX(_);});}},_lq=E(_kD);return _lq[0]==6?E(_lq[3])[0]==0?E(_lq[4])[0]==0?E(_kp):B(_kV(_)):B(_kV(_)):B(_kV(_));},_lr=E(_kE);return _lr[0]==4?E(_lr[3])[0]==0?E(_kp):B(_kT(_)):B(_kT(_));},_ls=E(_kD);switch(_ls[0]){case 4:return E(_ls[3])[0]==0?E(_kp):B(_kR(_));case 9:return E(_ls[3])[0]==0?E(_ls[4])[0]==0?E(_kp):B(_kR(_)):B(_kR(_));default:return new F(function(){return _kR(_);});}},_lt=E(_kE);return _lt[0]==9?E(_lt[3])[0]==0?E(_lt[4])[0]==0?E(_kp):B(_kP(_)):B(_kP(_)):B(_kP(_));},_lu=E(_kD);return _lu[0]==7?E(_lu[3])[0]==0?E(_kp):B(_kN(_)):B(_kN(_));},_lv=E(_kE);switch(_lv[0]){case 5:return E(_lv[3])[0]==0?E(_lv[4])[0]==0?E(_kp):B(_kL(_)):B(_kL(_));case 7:return E(_lv[3])[0]==0?E(_kp):B(_kL(_));default:return new F(function(){return _kL(_);});}},_lw=E(_kD);return _lw[0]==5?E(_lw[3])[0]==0?E(_lw[4])[0]==0?E(_kp):B(_kJ(_)):B(_kJ(_)):B(_kJ(_));},_lx=E(_kE);return _lx[0]==3?E(_lx[3])[0]==0?E(_kp):B(_kH(_)):B(_kH(_));},_ly=E(_kD);return _ly[0]==3?E(_ly[3])[0]==0?E(_kp):B(_kF(_)):B(_kF(_));}}},_lz=function(_lA,_lB,_lC){return [0,_lA,_lB,_lC];},_lD=new T(function(){return B(_ik("w_sk9q{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv ah73} [tv]"));}),_lE=new T(function(){return B(_ik("w_sk9m{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv ah74} [tv]"));}),_lF=function(_lG){return [0,function(_lH,_lI){return B(A(_lG,[_lH,_lI,_60]))[0]==0?false:true;},function(_lJ,_lK){return B(A(_lG,[_lJ,_lK,_60]))[0]==0?true:false;}];},_lL=new T(function(){return B(_lF(_ci));}),_l8=function(_lM,_lN,_lO,_lP,_lQ,_lR,_lS,_lT,_lU,_lV){var _lW=function(_lX,_lY){return new F(function(){return _an(_lQ,_lS,_lT,_lR,_lP,_lU,_lV,_lX);});};return function(_lZ,_m0){return new F(function(){return _lz(new T(function(){return B(_jK(function(_m1,_m2){return new F(function(){return _kq(_lM,_lN,_lO,_lP,_lQ,_lR,_lS,_lT,_lU,_lV,_m1,_m2);});},new T(function(){return B(_jf(_lL,_ha,new T(function(){return B(_j8(_lW));}),new T(function(){return B(_kj(_lW));}),_lQ,_lS,_lT,_lP,_lR,_lU,_lV));}),_lE,_lM,_lN,_lO,_lD,_lP,_lQ,_lR,_lS,_lT,_lU,_lV));}),_lZ,_m0);});};},_m3=function(_m4,_m5,_m6){var _m7=E(_m5);if(!_m7[0]){return [0];}else{var _m8=E(_m6);return _m8[0]==0?[0]:[1,new T(function(){return B(A(_m4,[_m7[1],_m8[1]]));}),new T(function(){return B(_m3(_m4,_m7[2],_m8[2]));})];}},_m9=function(_ma,_mb,_mc,_md,_me,_mf,_mg,_mh,_mi,_mj,_mk,_ml){var _mm=E(_mk);if(!_mm[0]){return E(_iV);}else{var _mn=_mm[1],_mo=E(_ml);if(!_mo[0]){return E(_iV);}else{var _mp=_mo[1];return B(_iW(_mn,0))!=B(_iW(_mp,0))?[0]:[1,new T(function(){return B(_m3(new T(function(){return B(_l8(_ma,_mb,_mc,_md,_me,_mf,_mg,_mh,_mi,_mj));}),_mn,_mp));})];}}},_mq=new T(function(){return B(_ik("w_soh7{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv anU5} [tv]"));}),_mr=new T(function(){return B(_ik("w_sohb{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv anU4} [tv]"));}),_ms=new T(function(){return B(_lF(_ci));}),_mt=function(_mu,_mv,_mw,_mx,_my,_mz,_mA,_mB,_mC,_mD){var _mE=new T(function(){return B(_iE(function(_mF,_mG){return new F(function(){return _m9(_mu,_mv,_mw,_mx,_my,_mz,_mA,_mB,_mC,_mD,_mF,_mG);});},new T(function(){return B(_i8(_ms,_ha,new T(function(){return B(_bU(_my,_mA,_mB,_mx,_mz,_mC,_mD));}),new T(function(){return B(_go(_my,_mA,_mB,_mx,_mz,_mC,_mD));}),_my,_mA,_mB,_mx,_mz,_mC,_mD));}),_mq,_mu,_mv,_mw,_mr,_mx,_my,_mz,_mA,_mB,_mC,_mD));});return function(_mH,_mI){var _mJ=E(_mH),_mK=_mJ[1],_mL=E(_mI),_mM=_mL[1];return B(_iW(_mK,0))!=B(_iW(_mM,0))?[0]:[1,[1,[0,_mE,_mJ[2],_mL[2]],new T(function(){return B(_m3(function(_fm,_dK){return [0,_mE,_fm,_dK];},_mK,_mM));})]];};},_mN=new T(function(){return B(_ik("w_sojJ{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  f{tv anTC} [tv]"));}),_mO=new T(function(){return B(_ik("w_sojN{v} [lid] main:AbstractSyntaxDataTypes.UniformlyEq{tc rA5}\n                  quant{tv anTB} [tv]"));}),_mP=function(_mQ,_mR,_mS,_mT,_mU,_mV,_mW,_mX,_mY,_mZ){var _n0=new T(function(){return B(_hE(new T(function(){return B(_mt(_mQ,_mR,_mS,_mT,_mU,_mV,_mW,_mX,_mY,_mZ));}),new T(function(){return B(_hp(_ms,_ha,new T(function(){return B(_cg(new T(function(){return B(_bU(_mU,_mW,_mX,_mT,_mV,_mY,_mZ));})));}),new T(function(){return B(_gY(new T(function(){return B(_go(_mU,_mW,_mX,_mT,_mV,_mY,_mZ));})));}),_mU,_mW,_mX,_mT,_mV,_mY,_mZ));}),_mN,_mQ,_mR,_mS,_mO,_mT,_mU,_mV,_mW,_mX,_mY,_mZ));});return function(_n1,_n2){var _n3=E(_n1),_n4=_n3[1],_n5=E(_n2),_n6=_n5[1];return B(_iW(_n4,0))!=B(_iW(_n6,0))?[0]:[1,[1,[0,_n0,_n3[2],_n5[2]],new T(function(){return B(_m3(function(_fm,_dK){return [0,_n0,_fm,_dK];},_n4,_n6));})]];};},_n7=function(_n8,_n9){while(1){var _na=E(_n9);if(!_na[0]){return false;}else{var _nb=E(_na[1]);if(!B(A(_dL,[_nb[1],_n8,_nb[2]]))){_n9=_na[2];continue;}else{return true;}}}},_nc=[0,_f],_nd=function(_ne,_nf,_ng,_nh,_ni,_nj,_nk,_nl,_nm,_nn,_no){var _np=E(_nh);return !B(A(_np[1],[new T(function(){return B(A(_nm,[_nn]));}),_no]))?!B(_n7(_nn,B(A(_nj,[_no]))))?[0,[1,[0,[0,_ne,[0,_nf,_ng,_np,_ni,_nj,_nk],_nl,_nm],_nn,_no],_f]]:[1,[1,_,[0,_ne,[0,_nf,_ng,_np,_ni,_nj,_nk],_nl,_nm],[3,_ng,_ni,_nn,_no]]]:E(_nc);},_nq=function(_nr){return new F(function(){return _2w("JudgementHandler.hs:(54,15)-(56,42)|case");});},_ns=new T(function(){return B(_nq(_));}),_nt=new T(function(){return B(unCStr(": empty list"));}),_nu=new T(function(){return B(unCStr("Prelude."));}),_nv=function(_nw){return new F(function(){return err(B(_1E(_nu,new T(function(){return B(_1E(_nw,_nt));},1))));});},_nx=new T(function(){return B(unCStr("head"));}),_ny=new T(function(){return B(_nv(_nx));}),_nz=function(_nA){return E(E(_nA)[2]);},_nB=function(_nC,_nD){while(1){var _nE=E(_nC);if(!_nE){return E(_nD);}else{var _nF=E(_nD);if(!_nF[0]){return [0];}else{_nC=_nE-1|0;_nD=_nF[2];continue;}}}},_nG=function(_nH,_nI){var _nJ=E(_nH)[1];return _nJ>=0?B(_nB(_nJ,_nI)):E(_nI);},_nK=function(_nL){return new F(function(){return _2w("JudgementHandler.hs:96:31-64|function conc");});},_nM=new T(function(){return B(_nK(_));}),_nN=function(_nO){var _nP=E(_nO);switch(_nP[0]){case 3:return [2,_,_nP];case 4:return [4,_,_nP,_6C];case 5:return [6,_,_nP,_6C,_6C];case 6:return [8,_,_nP,_6z];case 7:return [10,_,_nP,_6z,_6z];default:return E(_jT);}},_nQ=function(_nR){var _nS=E(_nR);if(!_nS[0]){return [0];}else{var _nT=E(_nS[1]);if(!_nT[0]){return [0];}else{return new F(function(){return _1E(_nT[1],new T(function(){return B(_nQ(_nS[2]));},1));});}}},_nU=function(_nV){var _nW=E(_nV);return [0,[1,[1,new T(function(){return B(_nQ(_nW[1]));})],_f],_nW[2]];},_nX=function(_nY,_nZ,_o0){return !B(_82(_nY,_nZ,_o0))?E(_o0):[1,_nZ,new T(function(){return B(_7q(function(_o1){return !B(A(_80,[_nY,_o1,_nZ]))?true:false;},_o0));})];},_o2=function(_o3,_o4,_o5,_o6,_o7,_o8,_o9){return function(_oa,_ob){var _oc=E(_oa);if(!_oc[0]){return new F(function(){return _nU(_ob);});}else{var _od=E(_ob);return [0,[1,[1,new T(function(){return B(_nX(new T(function(){return B(_j8(function(_oe,_of){return new F(function(){return _an(_o9,_o8,_o7,_o5,_o6,_o3,_o4,_oe);});}));}),_oc[1],B(_nQ(_od[1]))));})],_f],_od[2]];}};},_og=new T(function(){return B(_lF(_ci));}),_oh=function(_oi){return E(E(_oi)[1]);},_oj=function(_ok,_ol){var _om=E(_ok);if(!_om){return [0];}else{var _on=E(_ol);return _on[0]==0?[0]:[1,_on[1],new T(function(){return B(_oj(_om-1|0,_on[2]));})];}},_oo=function(_op,_oq){return _op<0?[0]:B(_oj(_op,_oq));},_or=function(_os,_ot){var _ou=E(_os)[1];return _ou>0?B(_oo(_ou,_ot)):[0];},_ov=function(_ow,_ox){return [1,_,_ow,_ox];},_oy=function(_oz){return E(E(_oz)[2]);},_oA=function(_oB){return E(E(_oB)[4]);},_oC=function(_oD,_oE,_oF){var _oG=E(_oD),_oH=E(_oG[2]);return new F(function(){return _nd(_oG[1],_oH[1],_oH[2],_oH[3],_oH[4],_oH[5],_oH[6],_oG[3],_oG[4],_oE,_oF);});},_oI=function(_oJ,_oK,_oL,_oM,_oN,_oO){var _oP=B(A(_oL,[_oN,_oO]));if(!_oP[0]){var _oQ=B(A(_oL,[_oO,_oN]));if(!_oQ[0]){var _oR=B(A(_oJ,[_oN,_oO]));if(!_oR[0]){return [1,[0,new T(function(){return B(_oA(_oK));}),_oN,_oO]];}else{var _oS=B(_oT([0,_oJ,_oK,_oL,_oM],_oR[1]));return _oS[0]==0?E(_oS):[1,[2,new T(function(){return B(_oA(_oK));}),_oS[1],_oN,_oO]];}}else{var _oU=E(_oQ[1]);return new F(function(){return _oC(_oU[1],_oU[2],_oU[3]);});}}else{var _oV=E(_oP[1]);return new F(function(){return _oC(_oV[1],_oV[2],_oV[3]);});}},_oW=function(_oX){return E(E(_oX)[6]);},_oT=function(_oY,_oZ){var _p0=E(_oZ);if(!_p0[0]){return E(_nc);}else{var _p1=E(_p0[1]),_p2=E(_p1[1]),_p3=B(_oI(_p2[1],_p2[2],_p2[3],_p2[4],_p1[2],_p1[3]));if(!_p3[0]){var _p4=_p3[1],_p5=B(_oT(_oY,B(_7T(function(_p6){var _p7=E(_p6),_p8=_p7[1];return [0,_p8,new T(function(){return B(A(_oW,[B(_oy(_p8)),_p4,_p7[2]]));}),new T(function(){return B(A(_oW,[B(_oy(_p8)),_p4,_p7[3]]));})];},_p0[2]))));if(!_p5[0]){var _p9=_p5[1];return [0,new T(function(){var _pa=function(_pb){var _pc=E(_pb);return _pc[0]==0?E(_p9):[1,new T(function(){var _pd=E(_pc[1]),_pe=_pd[1];return [0,_pe,_pd[2],new T(function(){return B(A(_oW,[B(_oy(_pe)),_p9,_pd[3]]));})];}),new T(function(){return B(_pa(_pc[2]));})];};return B(_pa(_p4));})];}else{return [1,new T(function(){return B(_ov(_oY,_p5[1]));})];}}else{return [1,[1,_,_p2,_p3[1]]];}}},_pf=function(_pg,_ph,_pi,_pj,_pk,_pl,_pm,_pn,_po,_pp,_pq,_pr){var _ps=new T(function(){return B(_nz(_pr));}),_pt=function(_pu,_pv){return new F(function(){return _an(_pm,_pl,_pk,_pi,_pj,_pg,_ph,_pu);});},_pw=new T(function(){return B(_jf(_og,_ha,new T(function(){return B(_j8(_pt));}),new T(function(){return B(_kj(_pt));}),_pm,_pl,_pk,_pj,_pi,_pg,_ph));}),_px=function(_py,_pz){return new F(function(){return _kq(_pq,_po,_pp,_pj,_pm,_pi,_pl,_pk,_pg,_ph,_py,_pz);});};return function(_pA,_pB,_pC){var _pD=new T(function(){return B(A(_pn,[_pC]));});return [0,new T(function(){return B(_m3(function(_pE,_pF){var _pG=B(A(new T(function(){return B(_o2(_pg,_ph,_pi,_pj,_pk,_pl,_pm));}),[new T(function(){var _pH=E(E(_pF)[1]);if(!_pH[0]){var _pI=[0];}else{var _pJ=E(_pH[1]),_pI=_pJ[0]==0?[0]:[1,new T(function(){var _pK=E(_pJ[1]);return _pK[0]==0?E(_ny):B(_cI(new T(function(){var _pL=E(B(A(_ps,[_pA]))[2]);if(!_pL[0]){var _pM=E(_nM);}else{var _pN=E(_pL[1]);if(!_pN[0]){var _pO=E(_nM);}else{var _pP=_pN[1];if(!E(_pN[2])[0]){var _pQ=B(_jE(_px,_pw,_pP,_pD));if(!_pQ[0]){var _pR=B(_jE(_px,_pw,_pD,_pP));if(!_pR[0]){var _pS=B(_px(_pP,_pD));if(!_pS[0]){var _pT=[0];}else{var _pU=B(_oT([0,_px,_pw,function(_pV,_pW){return new F(function(){return _jE(_px,_pw,_pV,_pW);});},_nN],_pS[1])),_pT=_pU[0]==0?E(_pU[1]):[0];}var _pX=_pT;}else{var _pY=E(_pR[1]),_pZ=E(_pY[1]),_q0=E(_pZ[2]),_q1=B(_nd(_pZ[1],_q0[1],_q0[2],_q0[3],_q0[4],_q0[5],_q0[6],_pZ[3],_pZ[4],_pY[2],_pY[3])),_pX=_q1[0]==0?E(_q1[1]):[0];}var _q2=_pX;}else{var _q3=E(_pQ[1]),_q4=E(_q3[1]),_q5=E(_q4[2]),_q6=B(_nd(_q4[1],_q5[1],_q5[2],_q5[3],_q5[4],_q5[5],_q5[6],_q4[3],_q4[4],_q3[2],_q3[3])),_q2=_q6[0]==0?E(_q6[1]):[0];}var _q7=_q2;}else{var _q7=E(_nM);}var _pO=_q7;}var _pM=_pO;}var _q8=_pM;return _q8;}),_pK[1]));})];}var _q9=_pI;return _q9;}),_pE])),_qa=_pG[2],_qb=E(E(_pF)[1]);if(!_qb[0]){return E(_ns);}else{var _qc=E(_qb[1]);if(!_qc[0]){return E(_qb[2])[0]==0?E(_pG):E(_ns);}else{var _qd=E(_pG[1]);if(!_qd[0]){return [0,_f,_qa];}else{var _qe=E(_qd[1]);if(!_qe[0]){return E(_pG);}else{var _qf=_qe[1],_qg=new T(function(){return [0,B(_iW(_qc[1],0))];});return [0,[1,[1,new T(function(){return B(_or(_qg,_qf));})],[1,[1,new T(function(){return B(_nG(_qg,_qf));})],_qd[2]]],_qa];}}}}},_pB,new T(function(){return B(A(new T(function(){return B(_oh(_pr));}),[_pA]));},1)));}),[0,new T(function(){return E(B(A(_ps,[_pA]))[1]);}),[1,[1,_pD,_f]]]];};},_qh=[1],_qi=new T(function(){return B(unCStr("Failure in Data.Map.balanceL"));}),_qj=function(_qk){return new F(function(){return err(_qi);});},_ql=new T(function(){return B(_qj(_));}),_qm=function(_qn,_qo,_qp){var _qq=E(_qp);if(!_qq[0]){var _qr=_qq[1],_qs=E(_qo);if(!_qs[0]){var _qt=_qs[1],_qu=_qs[2];if(_qt<=(imul(3,_qr)|0)){return [0,(1+_qt|0)+_qr|0,E(E(_qn)),E(_qs),E(_qq)];}else{var _qv=E(_qs[3]);if(!_qv[0]){var _qw=_qv[1],_qx=E(_qs[4]);if(!_qx[0]){var _qy=_qx[1],_qz=_qx[2],_qA=_qx[3];if(_qy>=(imul(2,_qw)|0)){var _qB=function(_qC){var _qD=E(_qx[4]);return _qD[0]==0?[0,(1+_qt|0)+_qr|0,E(_qz),E([0,(1+_qw|0)+_qC|0,E(_qu),E(_qv),E(_qA)]),E([0,(1+_qr|0)+_qD[1]|0,E(E(_qn)),E(_qD),E(_qq)])]:[0,(1+_qt|0)+_qr|0,E(_qz),E([0,(1+_qw|0)+_qC|0,E(_qu),E(_qv),E(_qA)]),E([0,1+_qr|0,E(E(_qn)),E(_qh),E(_qq)])];},_qE=E(_qA);return _qE[0]==0?B(_qB(_qE[1])):B(_qB(0));}else{return [0,(1+_qt|0)+_qr|0,E(_qu),E(_qv),E([0,(1+_qr|0)+_qy|0,E(E(_qn)),E(_qx),E(_qq)])];}}else{return E(_ql);}}else{return E(_ql);}}}else{return [0,1+_qr|0,E(E(_qn)),E(_qh),E(_qq)];}}else{var _qF=E(_qo);if(!_qF[0]){var _qG=_qF[1],_qH=_qF[2],_qI=_qF[4],_qJ=E(_qF[3]);if(!_qJ[0]){var _qK=_qJ[1],_qL=E(_qI);if(!_qL[0]){var _qM=_qL[1],_qN=_qL[2],_qO=_qL[3];if(_qM>=(imul(2,_qK)|0)){var _qP=function(_qQ){var _qR=E(_qL[4]);return _qR[0]==0?[0,1+_qG|0,E(_qN),E([0,(1+_qK|0)+_qQ|0,E(_qH),E(_qJ),E(_qO)]),E([0,1+_qR[1]|0,E(E(_qn)),E(_qR),E(_qh)])]:[0,1+_qG|0,E(_qN),E([0,(1+_qK|0)+_qQ|0,E(_qH),E(_qJ),E(_qO)]),E([0,1,E(E(_qn)),E(_qh),E(_qh)])];},_qS=E(_qO);return _qS[0]==0?B(_qP(_qS[1])):B(_qP(0));}else{return [0,1+_qG|0,E(_qH),E(_qJ),E([0,1+_qM|0,E(E(_qn)),E(_qL),E(_qh)])];}}else{return [0,3,E(_qH),E(_qJ),E([0,1,E(E(_qn)),E(_qh),E(_qh)])];}}else{var _qT=E(_qI);return _qT[0]==0?[0,3,E(_qT[2]),E([0,1,E(_qH),E(_qh),E(_qh)]),E([0,1,E(E(_qn)),E(_qh),E(_qh)])]:[0,2,E(E(_qn)),E(_qF),E(_qh)];}}else{return [0,1,E(E(_qn)),E(_qh),E(_qh)];}}},_qU=new T(function(){return B(unCStr("Failure in Data.Map.balanceR"));}),_qV=function(_qW){return new F(function(){return err(_qU);});},_qX=new T(function(){return B(_qV(_));}),_qY=function(_qZ,_r0,_r1){var _r2=E(_r0);if(!_r2[0]){var _r3=_r2[1],_r4=E(_r1);if(!_r4[0]){var _r5=_r4[1],_r6=_r4[2];if(_r5<=(imul(3,_r3)|0)){return [0,(1+_r3|0)+_r5|0,E(E(_qZ)),E(_r2),E(_r4)];}else{var _r7=E(_r4[3]);if(!_r7[0]){var _r8=_r7[1],_r9=_r7[2],_ra=_r7[3],_rb=E(_r4[4]);if(!_rb[0]){var _rc=_rb[1];if(_r8>=(imul(2,_rc)|0)){var _rd=function(_re){var _rf=E(_qZ),_rg=E(_r7[4]);return _rg[0]==0?[0,(1+_r3|0)+_r5|0,E(_r9),E([0,(1+_r3|0)+_re|0,E(_rf),E(_r2),E(_ra)]),E([0,(1+_rc|0)+_rg[1]|0,E(_r6),E(_rg),E(_rb)])]:[0,(1+_r3|0)+_r5|0,E(_r9),E([0,(1+_r3|0)+_re|0,E(_rf),E(_r2),E(_ra)]),E([0,1+_rc|0,E(_r6),E(_qh),E(_rb)])];},_rh=E(_ra);return _rh[0]==0?B(_rd(_rh[1])):B(_rd(0));}else{return [0,(1+_r3|0)+_r5|0,E(_r6),E([0,(1+_r3|0)+_r8|0,E(E(_qZ)),E(_r2),E(_r7)]),E(_rb)];}}else{return E(_qX);}}else{return E(_qX);}}}else{return [0,1+_r3|0,E(E(_qZ)),E(_r2),E(_qh)];}}else{var _ri=E(_r1);if(!_ri[0]){var _rj=_ri[1],_rk=_ri[2],_rl=_ri[4],_rm=E(_ri[3]);if(!_rm[0]){var _rn=_rm[1],_ro=_rm[2],_rp=_rm[3],_rq=E(_rl);if(!_rq[0]){var _rr=_rq[1];if(_rn>=(imul(2,_rr)|0)){var _rs=function(_rt){var _ru=E(_qZ),_rv=E(_rm[4]);return _rv[0]==0?[0,1+_rj|0,E(_ro),E([0,1+_rt|0,E(_ru),E(_qh),E(_rp)]),E([0,(1+_rr|0)+_rv[1]|0,E(_rk),E(_rv),E(_rq)])]:[0,1+_rj|0,E(_ro),E([0,1+_rt|0,E(_ru),E(_qh),E(_rp)]),E([0,1+_rr|0,E(_rk),E(_qh),E(_rq)])];},_rw=E(_rp);return _rw[0]==0?B(_rs(_rw[1])):B(_rs(0));}else{return [0,1+_rj|0,E(_rk),E([0,1+_rn|0,E(E(_qZ)),E(_qh),E(_rm)]),E(_rq)];}}else{return [0,3,E(_ro),E([0,1,E(E(_qZ)),E(_qh),E(_qh)]),E([0,1,E(_rk),E(_qh),E(_qh)])];}}else{var _rx=E(_rl);return _rx[0]==0?[0,3,E(_rk),E([0,1,E(E(_qZ)),E(_qh),E(_qh)]),E(_rx)]:[0,2,E(E(_qZ)),E(_qh),E(_ri)];}}else{return [0,1,E(E(_qZ)),E(_qh),E(_qh)];}}},_ry=function(_rz){return [0,1,E(E(_rz)),E(_qh),E(_qh)];},_rA=function(_rB,_rC){var _rD=E(_rC);if(!_rD[0]){return new F(function(){return _qm(_rD[2],B(_rA(_rB,_rD[3])),_rD[4]);});}else{return new F(function(){return _ry(_rB);});}},_rE=function(_rF,_rG){var _rH=E(_rG);if(!_rH[0]){return new F(function(){return _qY(_rH[2],_rH[3],B(_rE(_rF,_rH[4])));});}else{return new F(function(){return _ry(_rF);});}},_rI=function(_rJ,_rK,_rL,_rM,_rN){return new F(function(){return _qY(_rL,_rM,B(_rE(_rJ,_rN)));});},_rO=function(_rP,_rQ,_rR,_rS,_rT){return new F(function(){return _qm(_rR,B(_rA(_rP,_rS)),_rT);});},_rU=function(_rV,_rW,_rX,_rY,_rZ,_s0){var _s1=E(_rW);if(!_s1[0]){var _s2=_s1[1],_s3=_s1[2],_s4=_s1[3],_s5=_s1[4];if((imul(3,_s2)|0)>=_rX){if((imul(3,_rX)|0)>=_s2){return [0,(_s2+_rX|0)+1|0,E(E(_rV)),E(_s1),E([0,_rX,E(_rY),E(_rZ),E(_s0)])];}else{return new F(function(){return _qY(_s3,_s4,B(_rU(_rV,_s5,_rX,_rY,_rZ,_s0)));});}}else{return new F(function(){return _qm(_rY,B(_s6(_rV,_s2,_s3,_s4,_s5,_rZ)),_s0);});}}else{return new F(function(){return _rO(_rV,_rX,_rY,_rZ,_s0);});}},_s6=function(_s7,_s8,_s9,_sa,_sb,_sc){var _sd=E(_sc);if(!_sd[0]){var _se=_sd[1],_sf=_sd[2],_sg=_sd[3],_sh=_sd[4];if((imul(3,_s8)|0)>=_se){if((imul(3,_se)|0)>=_s8){return [0,(_s8+_se|0)+1|0,E(E(_s7)),E([0,_s8,E(_s9),E(_sa),E(_sb)]),E(_sd)];}else{return new F(function(){return _qY(_s9,_sa,B(_rU(_s7,_sb,_se,_sf,_sg,_sh)));});}}else{return new F(function(){return _qm(_sf,B(_s6(_s7,_s8,_s9,_sa,_sb,_sg)),_sh);});}}else{return new F(function(){return _rI(_s7,_s8,_s9,_sa,_sb);});}},_si=function(_sj,_sk,_sl){var _sm=E(_sk);if(!_sm[0]){var _sn=_sm[1],_so=_sm[2],_sp=_sm[3],_sq=_sm[4],_sr=E(_sl);if(!_sr[0]){var _ss=_sr[1],_st=_sr[2],_su=_sr[3],_sv=_sr[4];if((imul(3,_sn)|0)>=_ss){if((imul(3,_ss)|0)>=_sn){return [0,(_sn+_ss|0)+1|0,E(E(_sj)),E(_sm),E(_sr)];}else{return new F(function(){return _qY(_so,_sp,B(_rU(_sj,_sq,_ss,_st,_su,_sv)));});}}else{return new F(function(){return _qm(_st,B(_s6(_sj,_sn,_so,_sp,_sq,_su)),_sv);});}}else{return new F(function(){return _rI(_sj,_sn,_so,_sp,_sq);});}}else{return new F(function(){return _rA(_sj,_sl);});}},_sw=function(_sx,_sy,_sz,_sA){var _sB=E(_sA);if(!_sB[0]){var _sC=new T(function(){var _sD=B(_sw(_sB[1],_sB[2],_sB[3],_sB[4]));return [0,_sD[1],_sD[2]];});return [0,new T(function(){return E(E(_sC)[1]);}),new T(function(){return B(_qm(_sy,_sz,E(_sC)[2]));})];}else{return [0,_sy,_sz];}},_sE=function(_sF,_sG,_sH,_sI){var _sJ=E(_sH);if(!_sJ[0]){var _sK=new T(function(){var _sL=B(_sE(_sJ[1],_sJ[2],_sJ[3],_sJ[4]));return [0,_sL[1],_sL[2]];});return [0,new T(function(){return E(E(_sK)[1]);}),new T(function(){return B(_qY(_sG,E(_sK)[2],_sI));})];}else{return [0,_sG,_sI];}},_sM=function(_sN,_sO){var _sP=E(_sN);if(!_sP[0]){var _sQ=_sP[1],_sR=E(_sO);if(!_sR[0]){var _sS=_sR[1];if(_sQ<=_sS){var _sT=B(_sE(_sS,_sR[2],_sR[3],_sR[4]));return new F(function(){return _qm(_sT[1],_sP,_sT[2]);});}else{var _sU=B(_sw(_sQ,_sP[2],_sP[3],_sP[4]));return new F(function(){return _qY(_sU[1],_sU[2],_sR);});}}else{return E(_sP);}}else{return E(_sO);}},_sV=function(_sW,_sX,_sY,_sZ,_t0){var _t1=E(_sW);if(!_t1[0]){var _t2=_t1[1],_t3=_t1[2],_t4=_t1[3],_t5=_t1[4];if((imul(3,_t2)|0)>=_sX){if((imul(3,_sX)|0)>=_t2){return new F(function(){return _sM(_t1,[0,_sX,E(_sY),E(_sZ),E(_t0)]);});}else{return new F(function(){return _qY(_t3,_t4,B(_sV(_t5,_sX,_sY,_sZ,_t0)));});}}else{return new F(function(){return _qm(_sY,B(_t6(_t2,_t3,_t4,_t5,_sZ)),_t0);});}}else{return [0,_sX,E(_sY),E(_sZ),E(_t0)];}},_t6=function(_t7,_t8,_t9,_ta,_tb){var _tc=E(_tb);if(!_tc[0]){var _td=_tc[1],_te=_tc[2],_tf=_tc[3],_tg=_tc[4];if((imul(3,_t7)|0)>=_td){if((imul(3,_td)|0)>=_t7){return new F(function(){return _sM([0,_t7,E(_t8),E(_t9),E(_ta)],_tc);});}else{return new F(function(){return _qY(_t8,_t9,B(_sV(_ta,_td,_te,_tf,_tg)));});}}else{return new F(function(){return _qm(_te,B(_t6(_t7,_t8,_t9,_ta,_tf)),_tg);});}}else{return [0,_t7,E(_t8),E(_t9),E(_ta)];}},_th=function(_ti,_tj){var _tk=E(_ti);if(!_tk[0]){var _tl=_tk[1],_tm=_tk[2],_tn=_tk[3],_to=_tk[4],_tp=E(_tj);if(!_tp[0]){var _tq=_tp[1],_tr=_tp[2],_ts=_tp[3],_tt=_tp[4];if((imul(3,_tl)|0)>=_tq){if((imul(3,_tq)|0)>=_tl){return new F(function(){return _sM(_tk,_tp);});}else{return new F(function(){return _qY(_tm,_tn,B(_sV(_to,_tq,_tr,_ts,_tt)));});}}else{return new F(function(){return _qm(_tr,B(_t6(_tl,_tm,_tn,_to,_ts)),_tt);});}}else{return E(_tk);}}else{return E(_tj);}},_tu=function(_tv,_tw){var _tx=E(_tw);if(!_tx[0]){var _ty=_tx[2],_tz=_tx[3],_tA=_tx[4];if(!B(A(_tv,[_ty]))){return new F(function(){return _th(B(_tu(_tv,_tz)),B(_tu(_tv,_tA)));});}else{return new F(function(){return _si(_ty,B(_tu(_tv,_tz)),B(_tu(_tv,_tA)));});}}else{return [1];}},_tB=function(_tC,_tD,_tE,_tF){while(1){var _tG=E(_tF);if(!_tG[0]){_tC=_tG[1];_tD=_tG[2];_tE=_tG[3];_tF=_tG[4];continue;}else{return E(_tD);}}},_tH=function(_tI,_tJ){return [0];},_tK=function(_tL){return E(E(_tL)[1]);},_tM=function(_tN,_tO,_tP,_tQ,_tR,_tS,_tT,_tU,_tV,_tW,_tX){var _tY=new T(function(){return B(_pf(_tN,_tO,_tP,_tQ,_tR,_tS,_tT,_tU,_tV,_tW,_tX,_fr));}),_tZ=new T(function(){return B(_mP(_tX,_tV,_tW,_tQ,_tT,_tP,_tS,_tR,_tN,_tO));}),_u0=[0,_tZ,new T(function(){return B(_fa(_og,_ha,new T(function(){return B(_br(new T(function(){return B(_cg(new T(function(){return B(_bU(_tT,_tS,_tR,_tQ,_tP,_tN,_tO));})));})));}),new T(function(){return B(_fZ(new T(function(){return B(_gY(new T(function(){return B(_go(_tT,_tS,_tR,_tQ,_tP,_tN,_tO));})));})));}),_tT,_tS,_tR,_tQ,_tP,_tN,_tO));}),_tH,_60];return function(_u1,_u2,_u3){var _u4=B(_tu(function(_u5){var _u6=B(A(_tZ,[new T(function(){return B(A(_tY,[_u5,_u2,_u3]));}),_u5]));return _u6[0]==0?false:B(_oT(_u0,_u6[1]))[0]==0?true:false;},B(_tK(_u1))));if(!_u4[0]){var _u7=new T(function(){var _u8=E(_u4[4]);return _u8[0]==0?B(_tB(_u8[1],_u8[2],_u8[3],_u8[4])):E(_u4[2]);}),_u9=new T(function(){return B(A(_tY,[_u7,_u2,_u3]));}),_ua=B(A(_tZ,[_u7,_u9]));if(!_ua[0]){return [0];}else{var _ub=B(_oT(_u0,_ua[1]));if(!_ub[0]){var _uc=_ub[1];return [1,new T(function(){var _ud=E(E(_u9)[2]);return [0,new T(function(){return B(_7T(function(_ue){return new F(function(){return _df(_uc,_ue);});},_ud[1]));}),new T(function(){return B(_df(_uc,_ud[2]));})];})];}else{return [0];}}}else{return [0];}};},_uf=new T(function(){return B(unCStr("Set.findMin: empty set has no minimal element"));}),_ug=new T(function(){return B(err(_uf));}),_uh=function(_ui,_uj,_uk,_ul){while(1){var _um=E(_uk);if(!_um[0]){_ui=_um[1];_uj=_um[2];_uk=_um[3];_ul=_um[4];continue;}else{return E(_uj);}}},_un=function(_uo,_up){var _uq=B(_tu(function(_ur){return new F(function(){return _bv(E(_ur)[2],_uo);});},_up));if(!_uq[0]){var _us=E(_uq[3]);return _us[0]==0?B(_uh(_us[1],_us[2],_us[3],_us[4])):E(_uq[2]);}else{return E(_ug);}},_ut=[1,_f],_uu=function(_uv,_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD,_uE,_uF,_uG,_uH,_uI){var _uJ=E(_uI);if(!_uJ[0]){return [1,[0,[1,[1,[1,new T(function(){return B(A(_uC,[_uH]));}),_f]],_f],[1,[1,new T(function(){return B(A(_uC,[_uH]));}),_f]]]];}else{var _uK=function(_uL){var _uM=E(_uL);if(!_uM[0]){return E(_ut);}else{var _uN=E(_uM[1]),_uO=B(_uu(_uv,_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD,_uE,_uF,_uG,_uN[1],_uN[2]));if(!_uO[0]){return [0];}else{var _uP=B(_uK(_uM[2]));return _uP[0]==0?[0]:[1,[1,_uO[1],_uP[1]]];}}},_uQ=B(_uK(_uJ[2]));return _uQ[0]==0?[0]:B(A(_tM,[_uv,_uw,_ux,_uy,_uz,_uA,_uB,_uC,_uD,_uE,_uF,new T(function(){return B(_un(_uJ[1],_uG));}),_uQ[1],_uH]));}},_uR=2,_uS=new T(function(){return B(unCStr("analysis"));}),_uT=new T(function(){return B(unCStr("invalid"));}),_uU=function(_uV,_){return new F(function(){return _4U(_5T,_uT,_uV,_);});},_uW=[1,_0],_uX=[0,_uU,_uW],_uY=function(_uZ,_){return [0,_uX,_uZ];},_v0=new T(function(){return B(unCStr("rslt"));}),_v1=new T(function(){return B(unCStr("span"));}),_v2=function(_v3,_v4,_v5,_v6,_){var _v7=B(A(_v5,[_v6,_])),_v8=_v7,_v9=E(_v8),_va=E(_v9[1]),_vb=_va[1];return [0,[0,function(_vc,_){var _vd=jsFind(toJSStr(E(_v3))),_ve=_vd,_vf=E(_ve);if(!_vf[0]){return _vc;}else{var _vg=_vf[1];switch(E(_v4)){case 0:var _vh=B(A(_vb,[_vg,_])),_vi=_vh;return _vc;case 1:var _vj=E(_vg),_vk=_vj[1],_vl=jsGetChildren(_vk),_vm=_vl,_vn=E(_vm);if(!_vn[0]){var _vo=B(A(_vb,[_vj,_])),_vp=_vo;return _vc;}else{var _vq=jsCreateElem(toJSStr(E(_v1))),_vr=_vq,_vs=jsAddChildBefore(_vr,_vk,E(_vn[1])[1]),_vt=B(A(_vb,[[0,_vr],_])),_vu=_vt;return _vc;}break;default:var _vv=E(_vg),_vw=jsClearChildren(_vv[1]),_vx=B(A(_vb,[_vv,_])),_vy=_vx;return _vc;}}},_va[2]],_v9[2]];},_vz=function(_uV,_){return new F(function(){return _v2(_v0,_uR,_uY,_uV,_);});},_vA=new T(function(){return B(unCStr("div"));}),_vB=function(_vC,_vD,_vE,_){var _vF=jsCreateElem(toJSStr(E(_vA))),_vG=_vF,_vH=jsAppendChild(_vG,E(_vE)[1]),_vI=[0,_vG],_vJ=B(A(_vC,[_vD,_vI,_])),_vK=_vJ;return _vI;},_vL=function(_vM,_vN,_){var _vO=E(_vM);if(!_vO[0]){return _vN;}else{var _vP=B(_vB(_5T,_vO[1],_vN,_)),_vQ=_vP,_vR=B(_vL(_vO[2],_vN,_)),_vS=_vR;return _vN;}},_vT=function(_vU,_){var _vV=B(_vB(_5T,_f,_vU,_)),_vW=_vV,_vX=B(A(_41,[_4r,_vW,_4q,_v0,_])),_vY=_vX;return _vW;},_vZ=[0,_vT,_uW],_w0=function(_w1,_){return [0,_vZ,_w1];},_w2=new T(function(){return B(unCStr("root"));}),_w3=function(_w4,_w5){while(1){var _w6=E(_w4);if(!_w6[0]){return E(_w5)[0]==0?1:0;}else{var _w7=E(_w5);if(!_w7[0]){return 2;}else{var _w8=E(_w6[1])[1],_w9=E(_w7[1])[1];if(_w8!=_w9){return _w8>_w9?2:0;}else{_w4=_w6[2];_w5=_w7[2];continue;}}}}},_wa=new T(function(){return B(_1E(_f,_f));}),_wb=function(_wc,_wd,_we,_wf,_wg,_wh,_wi,_wj){var _wk=[0,_wc,_wd,_we],_wl=function(_wm){var _wn=E(_wf);if(!_wn[0]){var _wo=E(_wj);if(!_wo[0]){switch(B(_w3(_wc,_wg))){case 0:return [0,[0,_wg,_wh,_wi],_f];case 1:return _wd>=_wh?_wd!=_wh?[0,_wk,_f]:_we>=_wi?_we!=_wi?[0,_wk,_f]:[0,_wk,_wa]:[0,[0,_wg,_wh,_wi],_f]:[0,[0,_wg,_wh,_wi],_f];default:return [0,_wk,_f];}}else{return [0,[0,_wg,_wh,_wi],_wo];}}else{switch(B(_w3(_wc,_wg))){case 0:return [0,[0,_wg,_wh,_wi],_wj];case 1:return _wd>=_wh?_wd!=_wh?[0,_wk,_wn]:_we>=_wi?_we!=_wi?[0,_wk,_wn]:[0,_wk,new T(function(){return B(_1E(_wn,_wj));})]:[0,[0,_wg,_wh,_wi],_wj]:[0,[0,_wg,_wh,_wi],_wj];default:return [0,_wk,_wn];}}};if(!E(_wj)[0]){var _wp=E(_wf);return _wp[0]==0?B(_wl(_)):[0,_wk,_wp];}else{return new F(function(){return _wl(_);});}},_wq=function(_wr,_ws){while(1){var _wt=E(_wr);if(!_wt[0]){return E(_ws);}else{_wr=_wt[2];var _wu=[1,_wt[1],_ws];_ws=_wu;continue;}}},_wv=new T(function(){return B(_wq(_f,_f));}),_ww=new T(function(){return B(unCStr("Text.ParserCombinators.Parsec.Prim.many: combinator \'many\' is applied to a parser that accepts an empty string."));}),_wx=new T(function(){return B(err(_ww));}),_wy=function(_wz,_wA,_wB,_wC,_wD){var _wE=function(_wF,_wG,_wH){var _wI=[1,_wG,_wF];return new F(function(){return A(_wz,[_wH,new T(function(){var _wJ=E(_wF);return function(_wK,_wL,_wM){return new F(function(){return _wE(_wI,_wK,_wL);});};}),_wC,_wx,function(_wN){return new F(function(){return A(_wB,[new T(function(){return B(_wq(_wI,_f));}),_wH,new T(function(){var _wO=E(E(_wH)[2]),_wP=E(_wN),_wQ=E(_wP[1]),_wR=B(_wb(_wQ[1],_wQ[2],_wQ[3],_wP[2],_wO[1],_wO[2],_wO[3],_f));return [0,E(_wR[1]),_wR[2]];})]);});}]);});};return new F(function(){return A(_wz,[_wA,function(_wS,_wT,_wU){return new F(function(){return _wE(_f,_wS,_wT);});},_wC,_wx,function(_wV){return new F(function(){return A(_wD,[_wv,_wA,new T(function(){var _wW=E(E(_wA)[2]),_wX=E(_wV),_wY=E(_wX[1]),_wZ=B(_wb(_wY[1],_wY[2],_wY[3],_wX[2],_wW[1],_wW[2],_wW[3],_f));return [0,E(_wZ[1]),_wZ[2]];})]);});}]);});},_x0=function(_x1,_x2){var _x3=E(_x1),_x4=E(_x3[1]),_x5=E(_x2),_x6=E(_x5[1]),_x7=B(_wb(_x4[1],_x4[2],_x4[3],_x3[2],_x6[1],_x6[2],_x6[3],_x5[2]));return [0,E(_x7[1]),_x7[2]];},_x8=function(_x9,_xa,_xb,_xc,_xd,_xe){var _xf=function(_xg,_xh,_xi,_xj,_xk){return new F(function(){return _wy(_x9,_xh,function(_xl,_xm,_xn){return new F(function(){return A(_xi,[[1,_xg,_xl],_xm,new T(function(){var _xo=E(E(_xm)[2]),_xp=E(_xn),_xq=E(_xp[1]),_xr=B(_wb(_xq[1],_xq[2],_xq[3],_xp[2],_xo[1],_xo[2],_xo[3],_f));return [0,E(_xr[1]),_xr[2]];})]);});},_xj,function(_xs,_xt,_xu){return new F(function(){return A(_xk,[[1,_xg,_xs],_xt,new T(function(){var _xv=E(E(_xt)[2]),_xw=E(_xu),_xx=E(_xw[1]),_xy=B(_wb(_xx[1],_xx[2],_xx[3],_xw[2],_xv[1],_xv[2],_xv[3],_f));return [0,E(_xy[1]),_xy[2]];})]);});});});};return new F(function(){return A(_x9,[_xa,function(_xz,_xA,_xB){return new F(function(){return _xf(_xz,_xA,_xb,_xc,function(_xC,_xD,_xE){return new F(function(){return A(_xb,[_xC,_xD,new T(function(){return B(_x0(_xB,_xE));})]);});});});},_xc,function(_xF,_xG,_xH){return new F(function(){return _xf(_xF,_xG,_xb,_xc,function(_xI,_xJ,_xK){return new F(function(){return A(_xd,[_xI,_xJ,new T(function(){return B(_x0(_xH,_xK));})]);});});});},_xe]);});},_xL=function(_xM,_xN,_xO,_xP,_xQ){var _xR=function(_xS,_xT){return new F(function(){return A(_xM,[_xT,new T(function(){var _xU=E(_xS);return function(_xV,_xW,_xX){return new F(function(){return _xR(_f,_xW);});};}),_xP,_wx,function(_xY){return new F(function(){return A(_xO,[_0,_xT,new T(function(){var _xZ=E(E(_xT)[2]),_y0=E(_xY),_y1=E(_y0[1]),_y2=B(_wb(_y1[1],_y1[2],_y1[3],_y0[2],_xZ[1],_xZ[2],_xZ[3],_f));return [0,E(_y2[1]),_y2[2]];})]);});}]);});};return new F(function(){return A(_xM,[_xN,function(_y3,_y4,_y5){return new F(function(){return _xR(_f,_y4);});},_xP,_wx,function(_y6){return new F(function(){return A(_xQ,[_0,_xN,new T(function(){var _y7=E(E(_xN)[2]),_y8=E(_y6),_y9=E(_y8[1]),_ya=B(_wb(_y9[1],_y9[2],_y9[3],_y8[2],_y7[1],_y7[2],_y7[3],_f));return [0,E(_ya[1]),_ya[2]];})]);});}]);});},_yb=function(_yc,_yd,_ye,_yf,_yg,_yh,_yi){var _yj=function(_yk,_yl,_ym,_yn,_yo){var _yp=[1,_yk,_f],_yq=function(_yr,_ys,_yt,_yu){return new F(function(){return _yb(_yc,_yd,_yr,function(_yv,_yw,_yx){return new F(function(){return A(_ys,[[1,_yk,_yv],_yw,new T(function(){var _yy=E(E(_yw)[2]),_yz=E(_yx),_yA=E(_yz[1]),_yB=B(_wb(_yA[1],_yA[2],_yA[3],_yz[2],_yy[1],_yy[2],_yy[3],_f));return [0,E(_yB[1]),_yB[2]];})]);});},_yt,function(_yC,_yD,_yE){return new F(function(){return A(_yu,[[1,_yk,_yC],_yD,new T(function(){var _yF=E(E(_yD)[2]),_yG=E(_yE),_yH=E(_yG[1]),_yI=B(_wb(_yH[1],_yH[2],_yH[3],_yG[2],_yF[1],_yF[2],_yF[3],_f));return [0,E(_yI[1]),_yI[2]];})]);});},function(_yJ){return new F(function(){return A(_yu,[_yp,_yr,new T(function(){var _yK=E(E(_yr)[2]),_yL=_yK[1],_yM=_yK[2],_yN=_yK[3],_yO=E(_yJ),_yP=E(_yO[1]),_yQ=B(_wb(_yP[1],_yP[2],_yP[3],_yO[2],_yL,_yM,_yN,_f)),_yR=E(_yQ[1]),_yS=B(_wb(_yR[1],_yR[2],_yR[3],_yQ[2],_yL,_yM,_yN,_f));return [0,E(_yS[1]),_yS[2]];})]);});});});};return new F(function(){return A(_yd,[_yl,function(_yT,_yU,_yV){return new F(function(){return _yq(_yU,_ym,_yn,function(_yW,_yX,_yY){return new F(function(){return A(_ym,[_yW,_yX,new T(function(){return B(_x0(_yV,_yY));})]);});});});},_yn,function(_yZ,_z0,_z1){return new F(function(){return _yq(_z0,_ym,_yn,function(_z2,_z3,_z4){return new F(function(){return A(_yo,[_z2,_z3,new T(function(){return B(_x0(_z1,_z4));})]);});});});},function(_z5){return new F(function(){return A(_yo,[_yp,_yl,new T(function(){var _z6=E(E(_yl)[2]),_z7=E(_z5),_z8=E(_z7[1]),_z9=B(_wb(_z8[1],_z8[2],_z8[3],_z7[2],_z6[1],_z6[2],_z6[3],_f));return [0,E(_z9[1]),_z9[2]];})]);});}]);});};return new F(function(){return A(_yc,[_ye,function(_za,_zb,_zc){return new F(function(){return _yj(_za,_zb,_yf,_yg,function(_zd,_ze,_zf){return new F(function(){return A(_yf,[_zd,_ze,new T(function(){return B(_x0(_zc,_zf));})]);});});});},_yg,function(_zg,_zh,_zi){return new F(function(){return _yj(_zg,_zh,_yf,_yg,function(_zj,_zk,_zl){return new F(function(){return A(_yh,[_zj,_zk,new T(function(){return B(_x0(_zi,_zl));})]);});});});},_yi]);});},_zm=function(_zn,_zo){return new F(function(){return A(_zo,[_zn]);});},_zp=[0,34],_zq=[1,_zp,_f],_zr=[0,E(_f)],_zs=[1,_zr,_f],_zt=function(_zu,_zv){var _zw=_zu%_zv;if(_zu<=0){if(_zu>=0){return E(_zw);}else{if(_zv<=0){return E(_zw);}else{var _zx=E(_zw);return _zx==0?0:_zx+_zv|0;}}}else{if(_zv>=0){if(_zu>=0){return E(_zw);}else{if(_zv<=0){return E(_zw);}else{var _zy=E(_zw);return _zy==0?0:_zy+_zv|0;}}}else{var _zz=E(_zw);return _zz==0?0:_zz+_zv|0;}}},_zA=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_zB=new T(function(){return B(err(_zA));}),_zC=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_zD=new T(function(){return B(err(_zC));}),_zE=function(_zF,_zG){while(1){var _zH=E(_zF);if(!_zH[0]){return E(_zD);}else{var _zI=E(_zG);if(!_zI){return E(_zH[1]);}else{_zF=_zH[2];_zG=_zI-1|0;continue;}}}},_zJ=new T(function(){return B(unCStr("ACK"));}),_zK=new T(function(){return B(unCStr("BEL"));}),_zL=new T(function(){return B(unCStr("BS"));}),_zM=new T(function(){return B(unCStr("SP"));}),_zN=[1,_zM,_f],_zO=new T(function(){return B(unCStr("US"));}),_zP=[1,_zO,_zN],_zQ=new T(function(){return B(unCStr("RS"));}),_zR=[1,_zQ,_zP],_zS=new T(function(){return B(unCStr("GS"));}),_zT=[1,_zS,_zR],_zU=new T(function(){return B(unCStr("FS"));}),_zV=[1,_zU,_zT],_zW=new T(function(){return B(unCStr("ESC"));}),_zX=[1,_zW,_zV],_zY=new T(function(){return B(unCStr("SUB"));}),_zZ=[1,_zY,_zX],_A0=new T(function(){return B(unCStr("EM"));}),_A1=[1,_A0,_zZ],_A2=new T(function(){return B(unCStr("CAN"));}),_A3=[1,_A2,_A1],_A4=new T(function(){return B(unCStr("ETB"));}),_A5=[1,_A4,_A3],_A6=new T(function(){return B(unCStr("SYN"));}),_A7=[1,_A6,_A5],_A8=new T(function(){return B(unCStr("NAK"));}),_A9=[1,_A8,_A7],_Aa=new T(function(){return B(unCStr("DC4"));}),_Ab=[1,_Aa,_A9],_Ac=new T(function(){return B(unCStr("DC3"));}),_Ad=[1,_Ac,_Ab],_Ae=new T(function(){return B(unCStr("DC2"));}),_Af=[1,_Ae,_Ad],_Ag=new T(function(){return B(unCStr("DC1"));}),_Ah=[1,_Ag,_Af],_Ai=new T(function(){return B(unCStr("DLE"));}),_Aj=[1,_Ai,_Ah],_Ak=new T(function(){return B(unCStr("SI"));}),_Al=[1,_Ak,_Aj],_Am=new T(function(){return B(unCStr("SO"));}),_An=[1,_Am,_Al],_Ao=new T(function(){return B(unCStr("CR"));}),_Ap=[1,_Ao,_An],_Aq=new T(function(){return B(unCStr("FF"));}),_Ar=[1,_Aq,_Ap],_As=new T(function(){return B(unCStr("VT"));}),_At=[1,_As,_Ar],_Au=new T(function(){return B(unCStr("LF"));}),_Av=[1,_Au,_At],_Aw=new T(function(){return B(unCStr("HT"));}),_Ax=[1,_Aw,_Av],_Ay=[1,_zL,_Ax],_Az=[1,_zK,_Ay],_AA=[1,_zJ,_Az],_AB=new T(function(){return B(unCStr("ENQ"));}),_AC=[1,_AB,_AA],_AD=new T(function(){return B(unCStr("EOT"));}),_AE=[1,_AD,_AC],_AF=new T(function(){return B(unCStr("ETX"));}),_AG=[1,_AF,_AE],_AH=new T(function(){return B(unCStr("STX"));}),_AI=[1,_AH,_AG],_AJ=new T(function(){return B(unCStr("SOH"));}),_AK=[1,_AJ,_AI],_AL=new T(function(){return B(unCStr("NUL"));}),_AM=[1,_AL,_AK],_AN=[0,92],_AO=new T(function(){return B(unCStr("\\DEL"));}),_AP=new T(function(){return B(unCStr("\\a"));}),_AQ=new T(function(){return B(unCStr("\\\\"));}),_AR=new T(function(){return B(unCStr("\\SO"));}),_AS=new T(function(){return B(unCStr("\\r"));}),_AT=new T(function(){return B(unCStr("\\f"));}),_AU=new T(function(){return B(unCStr("\\v"));}),_AV=new T(function(){return B(unCStr("\\n"));}),_AW=new T(function(){return B(unCStr("\\t"));}),_AX=new T(function(){return B(unCStr("\\b"));}),_AY=function(_AZ,_B0){if(_AZ<=127){var _B1=E(_AZ);switch(_B1){case 92:return new F(function(){return _1E(_AQ,_B0);});break;case 127:return new F(function(){return _1E(_AO,_B0);});break;default:if(_B1<32){var _B2=E(_B1);switch(_B2){case 7:return new F(function(){return _1E(_AP,_B0);});break;case 8:return new F(function(){return _1E(_AX,_B0);});break;case 9:return new F(function(){return _1E(_AW,_B0);});break;case 10:return new F(function(){return _1E(_AV,_B0);});break;case 11:return new F(function(){return _1E(_AU,_B0);});break;case 12:return new F(function(){return _1E(_AT,_B0);});break;case 13:return new F(function(){return _1E(_AS,_B0);});break;case 14:return new F(function(){return _1E(_AR,new T(function(){var _B3=E(_B0);if(!_B3[0]){var _B4=[0];}else{var _B4=E(E(_B3[1])[1])==72?B(unAppCStr("\\&",_B3)):E(_B3);}return _B4;},1));});break;default:return new F(function(){return _1E([1,_AN,new T(function(){var _B5=_B2;return _B5>=0?B(_zE(_AM,_B5)):E(_zB);})],_B0);});}}else{return [1,[0,_B1],_B0];}}}else{return [1,_AN,new T(function(){var _B6=jsShowI(_AZ),_B7=_B6;return B(_1E(fromJSStr(_B7),new T(function(){var _B8=E(_B0);if(!_B8[0]){var _B9=[0];}else{var _Ba=E(_B8[1])[1];if(_Ba<48){var _Bb=E(_B8);}else{var _Bb=_Ba>57?E(_B8):B(unAppCStr("\\&",_B8));}var _Bc=_Bb,_Bd=_Bc,_B9=_Bd;}return _B9;},1)));})];}},_Be=new T(function(){return B(unCStr("\\\""));}),_Bf=function(_Bg,_Bh){var _Bi=E(_Bg);if(!_Bi[0]){return E(_Bh);}else{var _Bj=_Bi[2],_Bk=E(E(_Bi[1])[1]);if(_Bk==34){return new F(function(){return _1E(_Be,new T(function(){return B(_Bf(_Bj,_Bh));},1));});}else{return new F(function(){return _AY(_Bk,new T(function(){return B(_Bf(_Bj,_Bh));}));});}}},_Bl=function(_Bm,_Bn,_Bo,_Bp,_Bq,_Br,_Bs,_Bt,_Bu,_Bv){var _Bw=[0,_Bq,_Br,_Bs];return new F(function(){return A(_Bm,[new T(function(){return B(A(_Bn,[_Bp]));}),function(_Bx){var _By=E(_Bx);if(!_By[0]){return E(new T(function(){return B(A(_Bv,[[0,E(_Bw),_zs]]));}));}else{var _Bz=E(_By[1]),_BA=_Bz[1],_BB=_Bz[2];if(!B(A(_Bo,[_BA]))){return new F(function(){return A(_Bv,[[0,E(_Bw),[1,[0,E([1,_zp,new T(function(){return B(_Bf([1,_BA,_f],_zq));})])],_f]]]);});}else{var _BC=E(_BA);switch(E(_BC[1])){case 9:var _BD=[0,_Bq,_Br,(_Bs+8|0)-B(_zt(_Bs-1|0,8))|0];break;case 10:var _BD=E([0,_Bq,_Br+1|0,1]);break;default:var _BD=E([0,_Bq,_Br,_Bs+1|0]);}var _BE=_BD,_BF=[0,E(_BE),_f],_BG=[0,_BB,E(_BE),E(_Bt)];return new F(function(){return A(_Bu,[_BC,_BG,_BF]);});}}}]);});},_BH=function(_BI,_BJ){return E(_BI)[1]!=E(_BJ)[1];},_BK=function(_BL,_BM){return E(_BL)[1]==E(_BM)[1];},_BN=[0,_BK,_BH],_BO=new T(function(){return B(unCStr(" 	"));}),_BP=function(_BQ){return new F(function(){return _82(_BN,_BQ,_BO);});},_BR=function(_BS,_BT){return E(_BT);},_BU=function(_BV){return new F(function(){return err(_BV);});},_BW=function(_BX){return E(_BX);},_BY=[0,_zm,_BR,_BW,_BU],_BZ=function(_C0){return E(E(_C0)[3]);},_C1=function(_C2,_C3){var _C4=E(_C3);return _C4[0]==0?B(A(_BZ,[_C2,_Z])):B(A(_BZ,[_C2,[1,[0,_C4[1],_C4[2]]]]));},_C5=function(_C6){return new F(function(){return _C1(_BY,_C6);});},_C7=function(_C8,_C9,_Ca,_Cb,_Cc){var _Cd=E(_C8),_Ce=E(_Cd[2]);return new F(function(){return _Bl(_zm,_C5,_BP,_Cd[1],_Ce[1],_Ce[2],_Ce[3],_Cd[3],_C9,_Cc);});},_Cf=function(_Cg){return [0,_Cg,function(_Ch){return new F(function(){return _C1(_Cg,_Ch);});}];},_Ci=new T(function(){return B(_Cf(_BY));}),_Cj=function(_Ck){return [2,E(E(_Ck))];},_Cl=function(_Cm,_Cn){switch(E(_Cm)[0]){case 0:switch(E(_Cn)[0]){case 0:return false;case 1:return true;case 2:return true;default:return true;}break;case 1:return E(_Cn)[0]==1?false:true;case 2:return E(_Cn)[0]==2?false:true;default:return E(_Cn)[0]==3?false:true;}},_Co=[2,E(_f)],_Cp=function(_Ch){return new F(function(){return _Cl(_Co,_Ch);});},_Cq=function(_Cr,_Cs,_Ct){var _Cu=E(_Ct);if(!_Cu[0]){return [0,_Cr,[1,_Co,new T(function(){return B(_7q(_Cp,_Cs));})]];}else{var _Cv=_Cu[1],_Cw=E(_Cu[2]);if(!_Cw[0]){var _Cx=new T(function(){return [2,E(E(_Cv))];});return [0,_Cr,[1,_Cx,new T(function(){return B(_7q(function(_Ch){return new F(function(){return _Cl(_Cx,_Ch);});},_Cs));})]];}else{var _Cy=new T(function(){return [2,E(E(_Cv))];}),_Cz=function(_CA){var _CB=E(_CA);if(!_CB[0]){return [0,_Cr,[1,_Cy,new T(function(){return B(_7q(function(_Ch){return new F(function(){return _Cl(_Cy,_Ch);});},_Cs));})]];}else{var _CC=B(_Cz(_CB[2]));return [0,_CC[1],[1,new T(function(){return B(_Cj(_CB[1]));}),_CC[2]]];}};return new F(function(){return (function(_CD,_CE){var _CF=B(_Cz(_CE));return [0,_CF[1],[1,new T(function(){return B(_Cj(_CD));}),_CF[2]]];})(_Cw[1],_Cw[2]);});}}},_CG=function(_CH,_CI){var _CJ=E(_CH),_CK=B(_Cq(_CJ[1],_CJ[2],_CI));return [0,E(_CK[1]),_CK[2]];},_CL=function(_CM,_CN,_CO,_CP,_CQ,_CR,_CS){return new F(function(){return A(_CM,[_CO,_CP,_CQ,function(_CT,_CU,_CV){return new F(function(){return A(_CR,[_CT,_CU,new T(function(){var _CW=E(_CV),_CX=E(_CW[2]);if(!_CX[0]){var _CY=E(_CW);}else{var _CZ=B(_Cq(_CW[1],_CX,_CN)),_CY=[0,E(_CZ[1]),_CZ[2]];}var _D0=_CY;return _D0;})]);});},function(_D1){return new F(function(){return A(_CS,[new T(function(){return B(_CG(_D1,_CN));})]);});}]);});},_D2=function(_D3,_D4){return function(_D5,_D6,_D7,_D8,_D9){return new F(function(){return _CL(function(_Da,_Db,_Dc,_Dd,_De){var _Df=E(_D3),_Dg=E(_Da),_Dh=E(_Dg[2]);return new F(function(){return _Bl(E(_Df[1])[1],_Df[2],function(_Di){return new F(function(){return _BK(_Di,_D4);});},_Dg[1],_Dh[1],_Dh[2],_Dh[3],_Dg[3],_Db,_De);});},[1,[1,_zp,new T(function(){return B(_Bf([1,_D4,_f],_zq));})],_f],_D5,_D6,_D7,_D8,_D9);});};},_Dj=[0,10],_Dk=new T(function(){return B(unCStr("lf new-line"));}),_Dl=[1,_Dk,_f],_Dm=function(_Dn){return function(_Do,_Dp,_Dq,_Dr,_Ds){return new F(function(){return _CL(new T(function(){return B(_D2(_Dn,_Dj));}),_Dl,_Do,_Dp,_Dq,_Dr,_Ds);});};},_Dt=new T(function(){return B(_Dm(_Ci));}),_Du=new T(function(){return B(unCStr("digit"));}),_Dv=[1,_Du,_f],_Dw=function(_Dx){return new F(function(){return _C1(_BY,_Dx);});},_Dy=function(_Dz){var _DA=E(_Dz)[1];return _DA<48?false:_DA<=57;},_DB=function(_DC,_DD,_DE,_DF,_DG){var _DH=E(_DC),_DI=E(_DH[2]);return new F(function(){return _Bl(_zm,_Dw,_Dy,_DH[1],_DI[1],_DI[2],_DI[3],_DH[3],_DD,_DG);});},_DJ=function(_DK,_DL,_DM,_DN,_DO){return new F(function(){return _CL(_DB,_Dv,_DK,_DL,_DM,_DN,_DO);});},_DP=function(_DQ,_DR,_DS,_DT,_DU){return new F(function(){return _x8(_DJ,_DQ,_DR,_DS,_DT,_DU);});},_DV=new T(function(){return B(_Cf(_BY));}),_DW=[0,44],_DX=new T(function(){return B(_D2(_DV,_DW));}),_DY=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_DZ=new T(function(){return B(err(_DY));}),_E0=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_E1=new T(function(){return B(err(_E0));}),_E2=new T(function(){return B(_2w("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_E3=function(_E4,_E5){while(1){var _E6=(function(_E7,_E8){var _E9=E(_E7);switch(_E9[0]){case 0:var _Ea=E(_E8);if(!_Ea[0]){return [0];}else{_E4=B(A(_E9[1],[_Ea[1]]));_E5=_Ea[2];return null;}break;case 1:var _Eb=B(A(_E9[1],[_E8])),_Ec=_E8;_E4=_Eb;_E5=_Ec;return null;case 2:return [0];case 3:return [1,[0,_E9[1],_E8],new T(function(){return B(_E3(_E9[2],_E8));})];default:return E(_E9[1]);}})(_E4,_E5);if(_E6!=null){return _E6;}}},_Ed=function(_Ee,_Ef){var _Eg=function(_Eh){var _Ei=E(_Ef);if(_Ei[0]==3){return [3,_Ei[1],new T(function(){return B(_Ed(_Ee,_Ei[2]));})];}else{var _Ej=E(_Ee);if(_Ej[0]==2){return E(_Ei);}else{var _Ek=E(_Ei);if(_Ek[0]==2){return E(_Ej);}else{var _El=function(_Em){var _En=E(_Ek);if(_En[0]==4){return [1,function(_Eo){return [4,new T(function(){return B(_1E(B(_E3(_Ej,_Eo)),_En[1]));})];}];}else{var _Ep=E(_Ej);if(_Ep[0]==1){var _Eq=_Ep[1],_Er=E(_En);return _Er[0]==0?[1,function(_Es){return new F(function(){return _Ed(B(A(_Eq,[_Es])),_Er);});}]:[1,function(_Et){return new F(function(){return _Ed(B(A(_Eq,[_Et])),new T(function(){return B(A(_Er[1],[_Et]));}));});}];}else{var _Eu=E(_En);return _Eu[0]==0?E(_E2):[1,function(_Ev){return new F(function(){return _Ed(_Ep,new T(function(){return B(A(_Eu[1],[_Ev]));}));});}];}}},_Ew=E(_Ej);switch(_Ew[0]){case 1:var _Ex=E(_Ek);if(_Ex[0]==4){return [1,function(_Ey){return [4,new T(function(){return B(_1E(B(_E3(B(A(_Ew[1],[_Ey])),_Ey)),_Ex[1]));})];}];}else{return new F(function(){return _El(_);});}break;case 4:var _Ez=_Ew[1],_EA=E(_Ek);switch(_EA[0]){case 0:return [1,function(_EB){return [4,new T(function(){return B(_1E(_Ez,new T(function(){return B(_E3(_EA,_EB));},1)));})];}];case 1:return [1,function(_EC){return [4,new T(function(){return B(_1E(_Ez,new T(function(){return B(_E3(B(A(_EA[1],[_EC])),_EC));},1)));})];}];default:return [4,new T(function(){return B(_1E(_Ez,_EA[1]));})];}break;default:return new F(function(){return _El(_);});}}}}},_ED=E(_Ee);switch(_ED[0]){case 0:var _EE=E(_Ef);if(!_EE[0]){return [0,function(_EF){return new F(function(){return _Ed(B(A(_ED[1],[_EF])),new T(function(){return B(A(_EE[1],[_EF]));}));});}];}else{return new F(function(){return _Eg(_);});}break;case 3:return [3,_ED[1],new T(function(){return B(_Ed(_ED[2],_Ef));})];default:return new F(function(){return _Eg(_);});}},_EG=[0,41],_EH=[1,_EG,_f],_EI=[0,40],_EJ=[1,_EI,_f],_EK=function(_EL,_EM){var _EN=E(_EL);switch(_EN[0]){case 0:return [0,function(_EO){return new F(function(){return _EK(B(A(_EN[1],[_EO])),_EM);});}];case 1:return [1,function(_EP){return new F(function(){return _EK(B(A(_EN[1],[_EP])),_EM);});}];case 2:return [2];case 3:return new F(function(){return _Ed(B(A(_EM,[_EN[1]])),new T(function(){return B(_EK(_EN[2],_EM));}));});break;default:var _EQ=function(_ER){var _ES=E(_ER);if(!_ES[0]){return [0];}else{var _ET=E(_ES[1]);return new F(function(){return _1E(B(_E3(B(A(_EM,[_ET[1]])),_ET[2])),new T(function(){return B(_EQ(_ES[2]));},1));});}},_EU=B(_EQ(_EN[1]));return _EU[0]==0?[2]:[4,_EU];}},_EV=[2],_EW=function(_EX){return [3,_EX,_EV];},_EY=function(_EZ,_F0){var _F1=E(_EZ);if(!_F1){return new F(function(){return A(_F0,[_0]);});}else{return [0,function(_F2){return E(new T(function(){return B(_EY(_F1-1|0,_F0));}));}];}},_F3=function(_F4,_F5,_F6){return function(_F7){return new F(function(){return A(function(_F8,_F9,_Fa){while(1){var _Fb=(function(_Fc,_Fd,_Fe){var _Ff=E(_Fc);switch(_Ff[0]){case 0:var _Fg=E(_Fd);if(!_Fg[0]){return E(_F5);}else{_F8=B(A(_Ff[1],[_Fg[1]]));_F9=_Fg[2];var _Fh=_Fe+1|0;_Fa=_Fh;return null;}break;case 1:var _Fi=B(A(_Ff[1],[_Fd])),_Fj=_Fd,_Fh=_Fe;_F8=_Fi;_F9=_Fj;_Fa=_Fh;return null;case 2:return E(_F5);case 3:return function(_Fk){return new F(function(){return _EY(_Fe,function(_Fl){return E(new T(function(){return B(_EK(_Ff,_Fk));}));});});};default:return function(_lZ){return new F(function(){return _EK(_Ff,_lZ);});};}})(_F8,_F9,_Fa);if(_Fb!=null){return _Fb;}}},[new T(function(){return B(A(_F4,[_EW]));}),_F7,0,_F6]);});};},_Fm=function(_Fn){return new F(function(){return A(_Fn,[_f]);});},_Fo=function(_Fp,_Fq){var _Fr=function(_Fs){var _Ft=E(_Fs);if(!_Ft[0]){return E(_Fm);}else{var _Fu=_Ft[1];return !B(A(_Fp,[_Fu]))?E(_Fm):function(_Fv){return [0,function(_Fw){return E(new T(function(){return B(A(new T(function(){return B(_Fr(_Ft[2]));}),[function(_Fx){return new F(function(){return A(_Fv,[[1,_Fu,_Fx]]);});}]));}));}];};}};return function(_Fy){return new F(function(){return A(_Fr,[_Fy,_Fq]);});};},_Fz=[6],_FA=new T(function(){return B(unCStr("valDig: Bad base"));}),_FB=new T(function(){return B(err(_FA));}),_FC=function(_FD,_FE){var _FF=function(_FG,_FH){var _FI=E(_FG);if(!_FI[0]){return function(_FJ){return new F(function(){return A(_FJ,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{var _FK=E(_FI[1])[1],_FL=function(_FM){return function(_FN){return [0,function(_FO){return E(new T(function(){return B(A(new T(function(){return B(_FF(_FI[2],function(_FP){return new F(function(){return A(_FH,[[1,_FM,_FP]]);});}));}),[_FN]));}));}];};};switch(E(E(_FD)[1])){case 8:if(48>_FK){return function(_FQ){return new F(function(){return A(_FQ,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{if(_FK>55){return function(_FR){return new F(function(){return A(_FR,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{return new F(function(){return _FL([0,_FK-48|0]);});}}break;case 10:if(48>_FK){return function(_FS){return new F(function(){return A(_FS,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{if(_FK>57){return function(_FT){return new F(function(){return A(_FT,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{return new F(function(){return _FL([0,_FK-48|0]);});}}break;case 16:if(48>_FK){if(97>_FK){if(65>_FK){return function(_FU){return new F(function(){return A(_FU,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{if(_FK>70){return function(_FV){return new F(function(){return A(_FV,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{return new F(function(){return _FL([0,(_FK-65|0)+10|0]);});}}}else{if(_FK>102){if(65>_FK){return function(_FW){return new F(function(){return A(_FW,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{if(_FK>70){return function(_FX){return new F(function(){return A(_FX,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{return new F(function(){return _FL([0,(_FK-65|0)+10|0]);});}}}else{return new F(function(){return _FL([0,(_FK-97|0)+10|0]);});}}}else{if(_FK>57){if(97>_FK){if(65>_FK){return function(_FY){return new F(function(){return A(_FY,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{if(_FK>70){return function(_FZ){return new F(function(){return A(_FZ,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{return new F(function(){return _FL([0,(_FK-65|0)+10|0]);});}}}else{if(_FK>102){if(65>_FK){return function(_G0){return new F(function(){return A(_G0,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{if(_FK>70){return function(_G1){return new F(function(){return A(_G1,[new T(function(){return B(A(_FH,[_f]));})]);});};}else{return new F(function(){return _FL([0,(_FK-65|0)+10|0]);});}}}else{return new F(function(){return _FL([0,(_FK-97|0)+10|0]);});}}}else{return new F(function(){return _FL([0,_FK-48|0]);});}}break;default:return E(_FB);}}};return function(_G2){return new F(function(){return A(_FF,[_G2,_4r,function(_G3){var _G4=E(_G3);return _G4[0]==0?[2]:B(A(_FE,[_G4]));}]);});};},_G5=[0,10],_G6=[0,1],_G7=[0,2147483647],_G8=function(_G9,_Ga){while(1){var _Gb=E(_G9);if(!_Gb[0]){var _Gc=_Gb[1],_Gd=E(_Ga);if(!_Gd[0]){var _Ge=_Gd[1],_Gf=addC(_Gc,_Ge);if(!E(_Gf[2])){return [0,_Gf[1]];}else{_G9=[1,I_fromInt(_Gc)];_Ga=[1,I_fromInt(_Ge)];continue;}}else{_G9=[1,I_fromInt(_Gc)];_Ga=_Gd;continue;}}else{var _Gg=E(_Ga);if(!_Gg[0]){_G9=_Gb;_Ga=[1,I_fromInt(_Gg[1])];continue;}else{return [1,I_add(_Gb[1],_Gg[1])];}}}},_Gh=new T(function(){return B(_G8(_G7,_G6));}),_Gi=function(_Gj){var _Gk=E(_Gj);if(!_Gk[0]){var _Gl=E(_Gk[1]);return _Gl==(-2147483648)?E(_Gh):[0, -_Gl];}else{return [1,I_negate(_Gk[1])];}},_Gm=[0,10],_Gn=[0,0],_Go=function(_Gp){return [0,_Gp];},_Gq=function(_Gr,_Gs){while(1){var _Gt=E(_Gr);if(!_Gt[0]){var _Gu=_Gt[1],_Gv=E(_Gs);if(!_Gv[0]){var _Gw=_Gv[1];if(!(imul(_Gu,_Gw)|0)){return [0,imul(_Gu,_Gw)|0];}else{_Gr=[1,I_fromInt(_Gu)];_Gs=[1,I_fromInt(_Gw)];continue;}}else{_Gr=[1,I_fromInt(_Gu)];_Gs=_Gv;continue;}}else{var _Gx=E(_Gs);if(!_Gx[0]){_Gr=_Gt;_Gs=[1,I_fromInt(_Gx[1])];continue;}else{return [1,I_mul(_Gt[1],_Gx[1])];}}}},_Gy=function(_Gz,_GA,_GB){while(1){var _GC=E(_GB);if(!_GC[0]){return E(_GA);}else{var _GD=B(_G8(B(_Gq(_GA,_Gz)),B(_Go(E(_GC[1])[1]))));_GB=_GC[2];_GA=_GD;continue;}}},_GE=function(_GF){var _GG=new T(function(){return B(_Ed(B(_Ed([0,function(_GH){return E(E(_GH)[1])==45?[1,B(_FC(_G5,function(_GI){return new F(function(){return A(_GF,[[1,new T(function(){return B(_Gi(B(_Gy(_Gm,_Gn,_GI))));})]]);});}))]:[2];}],[0,function(_GJ){return E(E(_GJ)[1])==43?[1,B(_FC(_G5,function(_GK){return new F(function(){return A(_GF,[[1,new T(function(){return B(_Gy(_Gm,_Gn,_GK));})]]);});}))]:[2];}])),new T(function(){return [1,B(_FC(_G5,function(_GL){return new F(function(){return A(_GF,[[1,new T(function(){return B(_Gy(_Gm,_Gn,_GL));})]]);});}))];})));});return new F(function(){return _Ed([0,function(_GM){return E(E(_GM)[1])==101?E(_GG):[2];}],[0,function(_GN){return E(E(_GN)[1])==69?E(_GG):[2];}]);});},_GO=function(_GP){return new F(function(){return A(_GP,[_Z]);});},_GQ=function(_GR){return new F(function(){return A(_GR,[_Z]);});},_GS=function(_GT){return function(_GU){return E(E(_GU)[1])==46?[1,B(_FC(_G5,function(_GV){return new F(function(){return A(_GT,[[1,_GV]]);});}))]:[2];};},_GW=function(_GX){return [0,B(_GS(_GX))];},_GY=function(_GZ){return new F(function(){return _FC(_G5,function(_H0){return [1,B(_F3(_GW,_GO,function(_H1){return [1,B(_F3(_GE,_GQ,function(_H2){return new F(function(){return A(_GZ,[[5,[1,_H0,_H1,_H2]]]);});}))];}))];});});},_H3=function(_H4){return [1,B(_GY(_H4))];},_H5=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_H6=function(_H7){return new F(function(){return _82(_BN,_H7,_H5);});},_H8=[0,8],_H9=[0,16],_Ha=function(_Hb){var _Hc=function(_Hd){return new F(function(){return A(_Hb,[[5,[0,_H8,_Hd]]]);});},_He=function(_Hf){return new F(function(){return A(_Hb,[[5,[0,_H9,_Hf]]]);});};return function(_Hg){return E(E(_Hg)[1])==48?E([0,function(_Hh){switch(E(E(_Hh)[1])){case 79:return [1,B(_FC(_H8,_Hc))];case 88:return [1,B(_FC(_H9,_He))];case 111:return [1,B(_FC(_H8,_Hc))];case 120:return [1,B(_FC(_H9,_He))];default:return [2];}}]):[2];};},_Hi=function(_Hj){return [0,B(_Ha(_Hj))];},_Hk=true,_Hl=function(_Hm){var _Hn=new T(function(){return B(A(_Hm,[_H8]));}),_Ho=new T(function(){return B(A(_Hm,[_H9]));});return function(_Hp){switch(E(E(_Hp)[1])){case 79:return E(_Hn);case 88:return E(_Ho);case 111:return E(_Hn);case 120:return E(_Ho);default:return [2];}};},_Hq=function(_Hr){return [0,B(_Hl(_Hr))];},_Hs=[0,92],_Ht=function(_Hu){return new F(function(){return A(_Hu,[_G5]);});},_Hv=function(_Hw){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_4e(9,_Hw,_f));}))));});},_Hx=function(_Hy){var _Hz=E(_Hy);return _Hz[0]==0?E(_Hz[1]):I_toInt(_Hz[1]);},_HA=function(_HB,_HC){var _HD=E(_HB);if(!_HD[0]){var _HE=_HD[1],_HF=E(_HC);return _HF[0]==0?_HE<=_HF[1]:I_compareInt(_HF[1],_HE)>=0;}else{var _HG=_HD[1],_HH=E(_HC);return _HH[0]==0?I_compareInt(_HG,_HH[1])<=0:I_compare(_HG,_HH[1])<=0;}},_HI=function(_HJ){return [2];},_HK=function(_HL){var _HM=E(_HL);if(!_HM[0]){return E(_HI);}else{var _HN=_HM[1],_HO=E(_HM[2]);return _HO[0]==0?E(_HN):function(_HP){return new F(function(){return _Ed(B(A(_HN,[_HP])),new T(function(){return B(A(new T(function(){return B(_HK(_HO));}),[_HP]));}));});};}},_HQ=function(_HR){return [2];},_HS=function(_HT,_HU){var _HV=function(_HW,_HX){var _HY=E(_HW);if(!_HY[0]){return function(_HZ){return new F(function(){return A(_HZ,[_HT]);});};}else{var _I0=E(_HX);return _I0[0]==0?E(_HQ):E(_HY[1])[1]!=E(_I0[1])[1]?E(_HQ):function(_I1){return [0,function(_I2){return E(new T(function(){return B(A(new T(function(){return B(_HV(_HY[2],_I0[2]));}),[_I1]));}));}];};}};return function(_I3){return new F(function(){return A(_HV,[_HT,_I3,_HU]);});};},_I4=new T(function(){return B(unCStr("SOH"));}),_I5=[0,1],_I6=function(_I7){return [1,B(_HS(_I4,function(_I8){return E(new T(function(){return B(A(_I7,[_I5]));}));}))];},_I9=new T(function(){return B(unCStr("SO"));}),_Ia=[0,14],_Ib=function(_Ic){return [1,B(_HS(_I9,function(_Id){return E(new T(function(){return B(A(_Ic,[_Ia]));}));}))];},_Ie=function(_If){return [1,B(_F3(_I6,_Ib,_If))];},_Ig=new T(function(){return B(unCStr("NUL"));}),_Ih=[0,0],_Ii=function(_Ij){return [1,B(_HS(_Ig,function(_Ik){return E(new T(function(){return B(A(_Ij,[_Ih]));}));}))];},_Il=new T(function(){return B(unCStr("STX"));}),_Im=[0,2],_In=function(_Io){return [1,B(_HS(_Il,function(_Ip){return E(new T(function(){return B(A(_Io,[_Im]));}));}))];},_Iq=new T(function(){return B(unCStr("ETX"));}),_Ir=[0,3],_Is=function(_It){return [1,B(_HS(_Iq,function(_Iu){return E(new T(function(){return B(A(_It,[_Ir]));}));}))];},_Iv=new T(function(){return B(unCStr("EOT"));}),_Iw=[0,4],_Ix=function(_Iy){return [1,B(_HS(_Iv,function(_Iz){return E(new T(function(){return B(A(_Iy,[_Iw]));}));}))];},_IA=new T(function(){return B(unCStr("ENQ"));}),_IB=[0,5],_IC=function(_ID){return [1,B(_HS(_IA,function(_IE){return E(new T(function(){return B(A(_ID,[_IB]));}));}))];},_IF=new T(function(){return B(unCStr("ACK"));}),_IG=[0,6],_IH=function(_II){return [1,B(_HS(_IF,function(_IJ){return E(new T(function(){return B(A(_II,[_IG]));}));}))];},_IK=new T(function(){return B(unCStr("BEL"));}),_IL=[0,7],_IM=function(_IN){return [1,B(_HS(_IK,function(_IO){return E(new T(function(){return B(A(_IN,[_IL]));}));}))];},_IP=new T(function(){return B(unCStr("BS"));}),_IQ=[0,8],_IR=function(_IS){return [1,B(_HS(_IP,function(_IT){return E(new T(function(){return B(A(_IS,[_IQ]));}));}))];},_IU=new T(function(){return B(unCStr("HT"));}),_IV=[0,9],_IW=function(_IX){return [1,B(_HS(_IU,function(_IY){return E(new T(function(){return B(A(_IX,[_IV]));}));}))];},_IZ=new T(function(){return B(unCStr("LF"));}),_J0=[0,10],_J1=function(_J2){return [1,B(_HS(_IZ,function(_J3){return E(new T(function(){return B(A(_J2,[_J0]));}));}))];},_J4=new T(function(){return B(unCStr("VT"));}),_J5=[0,11],_J6=function(_J7){return [1,B(_HS(_J4,function(_J8){return E(new T(function(){return B(A(_J7,[_J5]));}));}))];},_J9=new T(function(){return B(unCStr("FF"));}),_Ja=[0,12],_Jb=function(_Jc){return [1,B(_HS(_J9,function(_Jd){return E(new T(function(){return B(A(_Jc,[_Ja]));}));}))];},_Je=new T(function(){return B(unCStr("CR"));}),_Jf=[0,13],_Jg=function(_Jh){return [1,B(_HS(_Je,function(_Ji){return E(new T(function(){return B(A(_Jh,[_Jf]));}));}))];},_Jj=new T(function(){return B(unCStr("SI"));}),_Jk=[0,15],_Jl=function(_Jm){return [1,B(_HS(_Jj,function(_Jn){return E(new T(function(){return B(A(_Jm,[_Jk]));}));}))];},_Jo=new T(function(){return B(unCStr("DLE"));}),_Jp=[0,16],_Jq=function(_Jr){return [1,B(_HS(_Jo,function(_Js){return E(new T(function(){return B(A(_Jr,[_Jp]));}));}))];},_Jt=new T(function(){return B(unCStr("DC1"));}),_Ju=[0,17],_Jv=function(_Jw){return [1,B(_HS(_Jt,function(_Jx){return E(new T(function(){return B(A(_Jw,[_Ju]));}));}))];},_Jy=new T(function(){return B(unCStr("DC2"));}),_Jz=[0,18],_JA=function(_JB){return [1,B(_HS(_Jy,function(_JC){return E(new T(function(){return B(A(_JB,[_Jz]));}));}))];},_JD=new T(function(){return B(unCStr("DC3"));}),_JE=[0,19],_JF=function(_JG){return [1,B(_HS(_JD,function(_JH){return E(new T(function(){return B(A(_JG,[_JE]));}));}))];},_JI=new T(function(){return B(unCStr("DC4"));}),_JJ=[0,20],_JK=function(_JL){return [1,B(_HS(_JI,function(_JM){return E(new T(function(){return B(A(_JL,[_JJ]));}));}))];},_JN=new T(function(){return B(unCStr("NAK"));}),_JO=[0,21],_JP=function(_JQ){return [1,B(_HS(_JN,function(_JR){return E(new T(function(){return B(A(_JQ,[_JO]));}));}))];},_JS=new T(function(){return B(unCStr("SYN"));}),_JT=[0,22],_JU=function(_JV){return [1,B(_HS(_JS,function(_JW){return E(new T(function(){return B(A(_JV,[_JT]));}));}))];},_JX=new T(function(){return B(unCStr("ETB"));}),_JY=[0,23],_JZ=function(_K0){return [1,B(_HS(_JX,function(_K1){return E(new T(function(){return B(A(_K0,[_JY]));}));}))];},_K2=new T(function(){return B(unCStr("CAN"));}),_K3=[0,24],_K4=function(_K5){return [1,B(_HS(_K2,function(_K6){return E(new T(function(){return B(A(_K5,[_K3]));}));}))];},_K7=new T(function(){return B(unCStr("EM"));}),_K8=[0,25],_K9=function(_Ka){return [1,B(_HS(_K7,function(_Kb){return E(new T(function(){return B(A(_Ka,[_K8]));}));}))];},_Kc=new T(function(){return B(unCStr("SUB"));}),_Kd=[0,26],_Ke=function(_Kf){return [1,B(_HS(_Kc,function(_Kg){return E(new T(function(){return B(A(_Kf,[_Kd]));}));}))];},_Kh=new T(function(){return B(unCStr("ESC"));}),_Ki=[0,27],_Kj=function(_Kk){return [1,B(_HS(_Kh,function(_Kl){return E(new T(function(){return B(A(_Kk,[_Ki]));}));}))];},_Km=new T(function(){return B(unCStr("FS"));}),_Kn=[0,28],_Ko=function(_Kp){return [1,B(_HS(_Km,function(_Kq){return E(new T(function(){return B(A(_Kp,[_Kn]));}));}))];},_Kr=new T(function(){return B(unCStr("GS"));}),_Ks=[0,29],_Kt=function(_Ku){return [1,B(_HS(_Kr,function(_Kv){return E(new T(function(){return B(A(_Ku,[_Ks]));}));}))];},_Kw=new T(function(){return B(unCStr("RS"));}),_Kx=[0,30],_Ky=function(_Kz){return [1,B(_HS(_Kw,function(_KA){return E(new T(function(){return B(A(_Kz,[_Kx]));}));}))];},_KB=new T(function(){return B(unCStr("US"));}),_KC=[0,31],_KD=function(_KE){return [1,B(_HS(_KB,function(_KF){return E(new T(function(){return B(A(_KE,[_KC]));}));}))];},_KG=new T(function(){return B(unCStr("SP"));}),_KH=[0,32],_KI=function(_KJ){return [1,B(_HS(_KG,function(_KK){return E(new T(function(){return B(A(_KJ,[_KH]));}));}))];},_KL=new T(function(){return B(unCStr("DEL"));}),_KM=[0,127],_KN=function(_KO){return [1,B(_HS(_KL,function(_KP){return E(new T(function(){return B(A(_KO,[_KM]));}));}))];},_KQ=[1,_KN,_f],_KR=[1,_KI,_KQ],_KS=[1,_KD,_KR],_KT=[1,_Ky,_KS],_KU=[1,_Kt,_KT],_KV=[1,_Ko,_KU],_KW=[1,_Kj,_KV],_KX=[1,_Ke,_KW],_KY=[1,_K9,_KX],_KZ=[1,_K4,_KY],_L0=[1,_JZ,_KZ],_L1=[1,_JU,_L0],_L2=[1,_JP,_L1],_L3=[1,_JK,_L2],_L4=[1,_JF,_L3],_L5=[1,_JA,_L4],_L6=[1,_Jv,_L5],_L7=[1,_Jq,_L6],_L8=[1,_Jl,_L7],_L9=[1,_Jg,_L8],_La=[1,_Jb,_L9],_Lb=[1,_J6,_La],_Lc=[1,_J1,_Lb],_Ld=[1,_IW,_Lc],_Le=[1,_IR,_Ld],_Lf=[1,_IM,_Le],_Lg=[1,_IH,_Lf],_Lh=[1,_IC,_Lg],_Li=[1,_Ix,_Lh],_Lj=[1,_Is,_Li],_Lk=[1,_In,_Lj],_Ll=[1,_Ii,_Lk],_Lm=[1,_Ie,_Ll],_Ln=new T(function(){return B(_HK(_Lm));}),_Lo=[0,1114111],_Lp=[0,34],_Lq=[0,39],_Lr=function(_Ls){var _Lt=new T(function(){return B(A(_Ls,[_IL]));}),_Lu=new T(function(){return B(A(_Ls,[_IQ]));}),_Lv=new T(function(){return B(A(_Ls,[_IV]));}),_Lw=new T(function(){return B(A(_Ls,[_J0]));}),_Lx=new T(function(){return B(A(_Ls,[_J5]));}),_Ly=new T(function(){return B(A(_Ls,[_Ja]));}),_Lz=new T(function(){return B(A(_Ls,[_Jf]));});return new F(function(){return _Ed([0,function(_LA){switch(E(E(_LA)[1])){case 34:return E(new T(function(){return B(A(_Ls,[_Lp]));}));case 39:return E(new T(function(){return B(A(_Ls,[_Lq]));}));case 92:return E(new T(function(){return B(A(_Ls,[_Hs]));}));case 97:return E(_Lt);case 98:return E(_Lu);case 102:return E(_Ly);case 110:return E(_Lw);case 114:return E(_Lz);case 116:return E(_Lv);case 118:return E(_Lx);default:return [2];}}],new T(function(){return B(_Ed([1,B(_F3(_Hq,_Ht,function(_LB){return [1,B(_FC(_LB,function(_LC){var _LD=B(_Gy(new T(function(){return B(_Go(E(_LB)[1]));}),_Gn,_LC));return !B(_HA(_LD,_Lo))?[2]:B(A(_Ls,[new T(function(){var _LE=B(_Hx(_LD));if(_LE>>>0>1114111){var _LF=B(_Hv(_LE));}else{var _LF=[0,_LE];}var _LG=_LF,_LH=_LG,_LI=_LH;return _LI;})]));}))];}))],new T(function(){return B(_Ed([0,function(_LJ){return E(E(_LJ)[1])==94?E([0,function(_LK){switch(E(E(_LK)[1])){case 64:return E(new T(function(){return B(A(_Ls,[_Ih]));}));case 65:return E(new T(function(){return B(A(_Ls,[_I5]));}));case 66:return E(new T(function(){return B(A(_Ls,[_Im]));}));case 67:return E(new T(function(){return B(A(_Ls,[_Ir]));}));case 68:return E(new T(function(){return B(A(_Ls,[_Iw]));}));case 69:return E(new T(function(){return B(A(_Ls,[_IB]));}));case 70:return E(new T(function(){return B(A(_Ls,[_IG]));}));case 71:return E(_Lt);case 72:return E(_Lu);case 73:return E(_Lv);case 74:return E(_Lw);case 75:return E(_Lx);case 76:return E(_Ly);case 77:return E(_Lz);case 78:return E(new T(function(){return B(A(_Ls,[_Ia]));}));case 79:return E(new T(function(){return B(A(_Ls,[_Jk]));}));case 80:return E(new T(function(){return B(A(_Ls,[_Jp]));}));case 81:return E(new T(function(){return B(A(_Ls,[_Ju]));}));case 82:return E(new T(function(){return B(A(_Ls,[_Jz]));}));case 83:return E(new T(function(){return B(A(_Ls,[_JE]));}));case 84:return E(new T(function(){return B(A(_Ls,[_JJ]));}));case 85:return E(new T(function(){return B(A(_Ls,[_JO]));}));case 86:return E(new T(function(){return B(A(_Ls,[_JT]));}));case 87:return E(new T(function(){return B(A(_Ls,[_JY]));}));case 88:return E(new T(function(){return B(A(_Ls,[_K3]));}));case 89:return E(new T(function(){return B(A(_Ls,[_K8]));}));case 90:return E(new T(function(){return B(A(_Ls,[_Kd]));}));case 91:return E(new T(function(){return B(A(_Ls,[_Ki]));}));case 92:return E(new T(function(){return B(A(_Ls,[_Kn]));}));case 93:return E(new T(function(){return B(A(_Ls,[_Ks]));}));case 94:return E(new T(function(){return B(A(_Ls,[_Kx]));}));case 95:return E(new T(function(){return B(A(_Ls,[_KC]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_Ln,[_Ls]));})));})));}));});},_LL=function(_LM){return new F(function(){return A(_LM,[_0]);});},_LN=function(_LO){var _LP=E(_LO);if(!_LP[0]){return E(_LL);}else{var _LQ=_LP[2],_LR=E(E(_LP[1])[1]);switch(_LR){case 9:return function(_LS){return [0,function(_LT){return E(new T(function(){return B(A(new T(function(){return B(_LN(_LQ));}),[_LS]));}));}];};case 10:return function(_LU){return [0,function(_LV){return E(new T(function(){return B(A(new T(function(){return B(_LN(_LQ));}),[_LU]));}));}];};case 11:return function(_LW){return [0,function(_LX){return E(new T(function(){return B(A(new T(function(){return B(_LN(_LQ));}),[_LW]));}));}];};case 12:return function(_LY){return [0,function(_LZ){return E(new T(function(){return B(A(new T(function(){return B(_LN(_LQ));}),[_LY]));}));}];};case 13:return function(_M0){return [0,function(_M1){return E(new T(function(){return B(A(new T(function(){return B(_LN(_LQ));}),[_M0]));}));}];};case 32:return function(_M2){return [0,function(_M3){return E(new T(function(){return B(A(new T(function(){return B(_LN(_LQ));}),[_M2]));}));}];};case 160:return function(_M4){return [0,function(_M5){return E(new T(function(){return B(A(new T(function(){return B(_LN(_LQ));}),[_M4]));}));}];};default:var _M6=u_iswspace(_LR),_M7=_M6;return E(_M7)==0?E(_LL):function(_M8){return [0,function(_M9){return E(new T(function(){return B(A(new T(function(){return B(_LN(_LQ));}),[_M8]));}));}];};}}},_Ma=function(_Mb){var _Mc=new T(function(){return B(_Ma(_Mb));}),_Md=[1,function(_Me){return new F(function(){return A(_LN,[_Me,function(_Mf){return E([0,function(_Mg){return E(E(_Mg)[1])==92?E(_Mc):[2];}]);}]);});}];return new F(function(){return _Ed([0,function(_Mh){return E(E(_Mh)[1])==92?E([0,function(_Mi){var _Mj=E(E(_Mi)[1]);switch(_Mj){case 9:return E(_Md);case 10:return E(_Md);case 11:return E(_Md);case 12:return E(_Md);case 13:return E(_Md);case 32:return E(_Md);case 38:return E(_Mc);case 160:return E(_Md);default:var _Mk=u_iswspace(_Mj),_Ml=_Mk;return E(_Ml)==0?[2]:E(_Md);}}]):[2];}],[0,function(_Mm){var _Mn=E(_Mm);return E(_Mn[1])==92?E(new T(function(){return B(_Lr(function(_Mo){return new F(function(){return A(_Mb,[[0,_Mo,_Hk]]);});}));})):B(A(_Mb,[[0,_Mn,_J]]));}]);});},_Mp=function(_Mq,_Mr){return new F(function(){return _Ma(function(_Ms){var _Mt=E(_Ms),_Mu=E(_Mt[1]);if(E(_Mu[1])==34){if(!E(_Mt[2])){return E(new T(function(){return B(A(_Mr,[[1,new T(function(){return B(A(_Mq,[_f]));})]]));}));}else{return new F(function(){return _Mp(function(_Mv){return new F(function(){return A(_Mq,[[1,_Mu,_Mv]]);});},_Mr);});}}else{return new F(function(){return _Mp(function(_Mw){return new F(function(){return A(_Mq,[[1,_Mu,_Mw]]);});},_Mr);});}});});},_Mx=new T(function(){return B(unCStr("_\'"));}),_My=function(_Mz){var _MA=u_iswalnum(_Mz),_MB=_MA;return E(_MB)==0?B(_82(_BN,[0,_Mz],_Mx)):true;},_MC=function(_MD){return new F(function(){return _My(E(_MD)[1]);});},_ME=new T(function(){return B(unCStr(",;()[]{}`"));}),_MF=new T(function(){return B(unCStr(".."));}),_MG=new T(function(){return B(unCStr("::"));}),_MH=new T(function(){return B(unCStr("->"));}),_MI=[0,64],_MJ=[1,_MI,_f],_MK=[0,126],_ML=[1,_MK,_f],_MM=new T(function(){return B(unCStr("=>"));}),_MN=[1,_MM,_f],_MO=[1,_ML,_MN],_MP=[1,_MJ,_MO],_MQ=[1,_MH,_MP],_MR=new T(function(){return B(unCStr("<-"));}),_MS=[1,_MR,_MQ],_MT=[0,124],_MU=[1,_MT,_f],_MV=[1,_MU,_MS],_MW=[1,_Hs,_f],_MX=[1,_MW,_MV],_MY=[0,61],_MZ=[1,_MY,_f],_N0=[1,_MZ,_MX],_N1=[1,_MG,_N0],_N2=[1,_MF,_N1],_N3=function(_N4){return new F(function(){return _Ed([1,function(_N5){return E(_N5)[0]==0?E(new T(function(){return B(A(_N4,[_Fz]));})):[2];}],new T(function(){return B(_Ed([0,function(_N6){return E(E(_N6)[1])==39?E([0,function(_N7){var _N8=E(_N7);switch(E(_N8[1])){case 39:return [2];case 92:return E(new T(function(){return B(_Lr(function(_N9){return [0,function(_Na){return E(E(_Na)[1])==39?E(new T(function(){return B(A(_N4,[[0,_N9]]));})):[2];}];}));}));default:return [0,function(_Nb){return E(E(_Nb)[1])==39?E(new T(function(){return B(A(_N4,[[0,_N8]]));})):[2];}];}}]):[2];}],new T(function(){return B(_Ed([0,function(_Nc){return E(E(_Nc)[1])==34?E(new T(function(){return B(_Mp(_4r,_N4));})):[2];}],new T(function(){return B(_Ed([0,function(_Nd){return !B(_82(_BN,_Nd,_ME))?[2]:B(A(_N4,[[2,[1,_Nd,_f]]]));}],new T(function(){return B(_Ed([0,function(_Ne){return !B(_82(_BN,_Ne,_H5))?[2]:[1,B(_Fo(_H6,function(_Nf){var _Ng=[1,_Ne,_Nf];return !B(_82(_7e,_Ng,_N2))?B(A(_N4,[[4,_Ng]])):B(A(_N4,[[2,_Ng]]));}))];}],new T(function(){return B(_Ed([0,function(_Nh){var _Ni=E(_Nh),_Nj=_Ni[1],_Nk=u_iswalpha(_Nj),_Nl=_Nk;return E(_Nl)==0?E(_Nj)==95?[1,B(_Fo(_MC,function(_Nm){return new F(function(){return A(_N4,[[3,[1,_Ni,_Nm]]]);});}))]:[2]:[1,B(_Fo(_MC,function(_Nn){return new F(function(){return A(_N4,[[3,[1,_Ni,_Nn]]]);});}))];}],new T(function(){return [1,B(_F3(_Hi,_H3,_N4))];})));})));})));})));})));}));});},_No=[0,0],_Np=function(_Nq,_Nr){return function(_Ns){return new F(function(){return A(_LN,[_Ns,function(_Nt){return E(new T(function(){return B(_N3(function(_Nu){var _Nv=E(_Nu);return _Nv[0]==2?!B(_bv(_Nv[1],_EJ))?[2]:E(new T(function(){return B(A(_Nq,[_No,function(_Nw){return [1,function(_Nx){return new F(function(){return A(_LN,[_Nx,function(_Ny){return E(new T(function(){return B(_N3(function(_Nz){var _NA=E(_Nz);return _NA[0]==2?!B(_bv(_NA[1],_EH))?[2]:E(new T(function(){return B(A(_Nr,[_Nw]));})):[2];}));}));}]);});}];}]));})):[2];}));}));}]);});};},_NB=function(_NC,_ND,_NE){var _NF=function(_NG,_NH){return new F(function(){return _Ed([1,function(_NI){return new F(function(){return A(_LN,[_NI,function(_NJ){return E(new T(function(){return B(_N3(function(_NK){var _NL=E(_NK);if(_NL[0]==4){var _NM=E(_NL[1]);if(!_NM[0]){return new F(function(){return A(_NC,[_NL,_NG,_NH]);});}else{return E(E(_NM[1])[1])==45?E(_NM[2])[0]==0?E([1,function(_NN){return new F(function(){return A(_LN,[_NN,function(_NO){return E(new T(function(){return B(_N3(function(_NP){return new F(function(){return A(_NC,[_NP,_NG,function(_NQ){return new F(function(){return A(_NH,[new T(function(){return [0, -E(_NQ)[1]];})]);});}]);});}));}));}]);});}]):B(A(_NC,[_NL,_NG,_NH])):B(A(_NC,[_NL,_NG,_NH]));}}else{return new F(function(){return A(_NC,[_NL,_NG,_NH]);});}}));}));}]);});}],new T(function(){return [1,B(_Np(_NF,_NH))];}));});};return new F(function(){return _NF(_ND,_NE);});},_NR=function(_NS,_NT){return [2];},_NU=function(_NV){var _NW=E(_NV);return _NW[0]==0?[1,new T(function(){return B(_Gy(new T(function(){return B(_Go(E(_NW[1])[1]));}),_Gn,_NW[2]));})]:E(_NW[2])[0]==0?E(_NW[3])[0]==0?[1,new T(function(){return B(_Gy(_Gm,_Gn,_NW[1]));})]:[0]:[0];},_NX=function(_NY){var _NZ=E(_NY);if(_NZ[0]==5){var _O0=B(_NU(_NZ[1]));return _O0[0]==0?E(_NR):function(_O1,_O2){return new F(function(){return A(_O2,[new T(function(){return [0,B(_Hx(_O0[1]))];})]);});};}else{return E(_NR);}},_O3=function(_O4){return [1,function(_O5){return new F(function(){return A(_LN,[_O5,function(_O6){return E([3,_O4,_EV]);}]);});}];},_O7=new T(function(){return B(_NB(_NX,_No,_O3));}),_O8=function(_O9){while(1){var _Oa=(function(_Ob){var _Oc=E(_Ob);if(!_Oc[0]){return [0];}else{var _Od=_Oc[2],_Oe=E(_Oc[1]);if(!E(_Oe[2])[0]){return [1,_Oe[1],new T(function(){return B(_O8(_Od));})];}else{_O9=_Od;return null;}}})(_O9);if(_Oa!=null){return _Oa;}}},_Of=function(_Og){var _Oh=B(_O8(B(_E3(_O7,_Og))));return _Oh[0]==0?E(_DZ):E(_Oh[2])[0]==0?E(_Oh[1]):E(_E1);},_Oi=function(_Oj,_Ok,_Ol,_Om,_On,_Oo){var _Op=function(_Oq){var _Or=[0,_Oj,new T(function(){return B(_7T(_Of,_Oq));})];return function(_Os,_Ot,_Ou,_Ov,_Ow){return new F(function(){return A(_Dt,[_Os,function(_Ox,_Oy,_Oz){return new F(function(){return A(_Ot,[_Or,_Oy,new T(function(){var _OA=E(E(_Oy)[2]),_OB=E(_Oz),_OC=E(_OB[1]),_OD=B(_wb(_OC[1],_OC[2],_OC[3],_OB[2],_OA[1],_OA[2],_OA[3],_f));return [0,E(_OD[1]),_OD[2]];})]);});},_Ow,function(_OE,_OF,_OG){return new F(function(){return A(_Ov,[_Or,_OF,new T(function(){var _OH=E(E(_OF)[2]),_OI=E(_OG),_OJ=E(_OI[1]),_OK=B(_wb(_OJ[1],_OJ[2],_OJ[3],_OI[2],_OH[1],_OH[2],_OH[3],_f));return [0,E(_OK[1]),_OK[2]];})]);});},_Ow]);});};},_OL=function(_OM,_ON,_OO,_OP,_OQ){var _OR=function(_OS,_OT,_OU){return new F(function(){return A(_Op,[_OS,_OT,_ON,_OO,function(_OV,_OW,_OX){return new F(function(){return A(_OP,[_OV,_OW,new T(function(){return B(_x0(_OU,_OX));})]);});},function(_OY){return new F(function(){return A(_OQ,[new T(function(){return B(_x0(_OU,_OY));})]);});}]);});},_OZ=function(_P0){return new F(function(){return _OR(_f,_OM,new T(function(){var _P1=E(E(_OM)[2]),_P2=E(_P0),_P3=E(_P2[1]),_P4=B(_wb(_P3[1],_P3[2],_P3[3],_P2[2],_P1[1],_P1[2],_P1[3],_f));return [0,E(_P4[1]),_P4[2]];}));});};return new F(function(){return _yb(_DP,_DX,_OM,function(_P5,_P6,_P7){return new F(function(){return A(_Op,[_P5,_P6,_ON,_OO,function(_P8,_P9,_Pa){return new F(function(){return A(_ON,[_P8,_P9,new T(function(){return B(_x0(_P7,_Pa));})]);});},function(_Pb){return new F(function(){return A(_OO,[new T(function(){return B(_x0(_P7,_Pb));})]);});}]);});},_OZ,_OR,_OZ);});};return new F(function(){return _xL(_C7,_Ok,function(_Pc,_Pd,_Pe){return new F(function(){return _OL(_Pd,_Ol,_Om,function(_Pf,_Pg,_Ph){return new F(function(){return A(_Ol,[_Pf,_Pg,new T(function(){return B(_x0(_Pe,_Ph));})]);});},function(_Pi){return new F(function(){return A(_Om,[new T(function(){return B(_x0(_Pe,_Pi));})]);});});});},_Om,function(_Pj,_Pk,_Pl){return new F(function(){return _OL(_Pk,_Ol,_Om,function(_Pm,_Pn,_Po){return new F(function(){return A(_On,[_Pm,_Pn,new T(function(){return B(_x0(_Pl,_Po));})]);});},function(_Pp){return new F(function(){return A(_Oo,[new T(function(){return B(_x0(_Pl,_Pp));})]);});});});});});},_Pq=new T(function(){return B(unCStr("letter or digit"));}),_Pr=[1,_Pq,_f],_Ps=function(_Pt){var _Pu=u_iswalnum(E(_Pt)[1]),_Pv=_Pu;return E(_Pv)==0?false:true;},_Pw=function(_Px,_Py,_Pz,_PA,_PB){var _PC=E(_Px),_PD=E(_PC[2]);return new F(function(){return _Bl(_zm,_Dw,_Ps,_PC[1],_PD[1],_PD[2],_PD[3],_PC[3],_Py,_PB);});},_PE=function(_PF,_PG,_PH,_PI,_PJ){return new F(function(){return _CL(_Pw,_Pr,_PF,_PG,_PH,_PI,_PJ);});},_PK=function(_PL,_PM,_PN,_PO,_PP){return new F(function(){return _x8(_PE,_PL,function(_PQ,_PR,_PS){return new F(function(){return _Oi(_PQ,_PR,_PM,_PN,function(_PT,_PU,_PV){return new F(function(){return A(_PM,[_PT,_PU,new T(function(){return B(_x0(_PS,_PV));})]);});},function(_PW){return new F(function(){return A(_PN,[new T(function(){return B(_x0(_PS,_PW));})]);});});});},_PP,function(_PX,_PY,_PZ){return new F(function(){return _Oi(_PX,_PY,_PM,_PN,function(_Q0,_Q1,_Q2){return new F(function(){return A(_PO,[_Q0,_Q1,new T(function(){return B(_x0(_PZ,_Q2));})]);});},function(_Q3){return new F(function(){return A(_PP,[new T(function(){return B(_x0(_PZ,_Q3));})]);});});});},_PP);});},_Q4=new T(function(){return B(unCStr("SHOW"));}),_Q5=[0,_Q4,_f],_Q6=function(_Q7,_Q8,_Q9,_Qa){var _Qb=function(_Qc){return new F(function(){return A(_Qa,[[0,_Q7,_Q5],_Q8,new T(function(){var _Qd=E(E(_Q8)[2]),_Qe=_Qd[1],_Qf=_Qd[2],_Qg=_Qd[3],_Qh=E(_Qc),_Qi=E(_Qh[1]),_Qj=B(_wb(_Qi[1],_Qi[2],_Qi[3],_Qh[2],_Qe,_Qf,_Qg,_f)),_Qk=E(_Qj[1]),_Ql=B(_wb(_Qk[1],_Qk[2],_Qk[3],_Qj[2],_Qe,_Qf,_Qg,_f));return [0,E(_Ql[1]),_Ql[2]];})]);});};return new F(function(){return _PK(_Q8,function(_Qm,_Qn,_Qo){return new F(function(){return A(_Q9,[[0,_Q7,_Qm],_Qn,new T(function(){var _Qp=E(E(_Qn)[2]),_Qq=E(_Qo),_Qr=E(_Qq[1]),_Qs=B(_wb(_Qr[1],_Qr[2],_Qr[3],_Qq[2],_Qp[1],_Qp[2],_Qp[3],_f));return [0,E(_Qs[1]),_Qs[2]];})]);});},_Qb,function(_Qt,_Qu,_Qv){return new F(function(){return A(_Qa,[[0,_Q7,_Qt],_Qu,new T(function(){var _Qw=E(E(_Qu)[2]),_Qx=E(_Qv),_Qy=E(_Qx[1]),_Qz=B(_wb(_Qy[1],_Qy[2],_Qy[3],_Qx[2],_Qw[1],_Qw[2],_Qw[3],_f));return [0,E(_Qz[1]),_Qz[2]];})]);});},_Qb);});},_QA=new T(function(){return B(unCStr("sS"));}),_QB=[0,58],_QC=new T(function(){return B(_D2(_Ci,_QB));}),_QD=[1,_Pq,_f],_QE=function(_QF,_QG,_QH,_QI,_QJ,_QK,_QL,_QM,_QN){var _QO=function(_QP,_QQ){var _QR=new T(function(){var _QS=B(_Cq(_QP,_QQ,_QD));return [0,E(_QS[1]),_QS[2]];});return new F(function(){return A(_QC,[[0,_QF,E([0,_QG,_QH,_QI]),E(_QJ)],_QK,_QL,function(_QT,_QU,_QV){return new F(function(){return A(_QM,[_QT,_QU,new T(function(){return B(_x0(_QR,_QV));})]);});},function(_QW){return new F(function(){return A(_QN,[new T(function(){return B(_x0(_QR,_QW));})]);});}]);});},_QX=E(_QF);if(!_QX[0]){return new F(function(){return _QO([0,_QG,_QH,_QI],_zs);});}else{var _QY=_QX[2],_QZ=E(_QX[1]),_R0=_QZ[1],_R1=u_iswalnum(_R0),_R2=_R1;if(!E(_R2)){return new F(function(){return _QO([0,_QG,_QH,_QI],[1,[0,E([1,_zp,new T(function(){return B(_Bf([1,_QZ,_f],_zq));})])],_f]);});}else{switch(E(_R0)){case 9:var _R3=[0,_QG,_QH,(_QI+8|0)-B(_zt(_QI-1|0,8))|0];break;case 10:var _R3=[0,_QG,_QH+1|0,1];break;default:var _R3=[0,_QG,_QH,_QI+1|0];}var _R4=_R3,_R5=[0,E(_R4),_f],_R6=[0,_QY,E(_R4),E(_QJ)];return new F(function(){return A(_QK,[_QZ,_R6,_R5]);});}}},_R7=function(_R8,_R9,_Ra,_Rb,_Rc){var _Rd=E(_R8),_Re=E(_Rd[2]);return new F(function(){return _QE(_Rd[1],_Re[1],_Re[2],_Re[3],_Rd[3],_R9,_Ra,_Rb,_Rc);});},_Rf=function(_Rg,_Rh,_Ri,_Rj,_Rk,_Rl,_Rm){var _Rn=function(_Ro,_Rp,_Rq,_Rr,_Rs,_Rt){return new F(function(){return _Ru(_Rp,function(_Rv,_Rw,_Rx){return new F(function(){return A(_Rq,[[1,_Ro,_Rv],_Rw,new T(function(){var _Ry=E(E(_Rw)[2]),_Rz=E(_Rx),_RA=E(_Rz[1]),_RB=B(_wb(_RA[1],_RA[2],_RA[3],_Rz[2],_Ry[1],_Ry[2],_Ry[3],_f));return [0,E(_RB[1]),_RB[2]];})]);});},_Rr,function(_RC,_RD,_RE){return new F(function(){return A(_Rs,[[1,_Ro,_RC],_RD,new T(function(){var _RF=E(E(_RD)[2]),_RG=E(_RE),_RH=E(_RG[1]),_RI=B(_wb(_RH[1],_RH[2],_RH[3],_RG[2],_RF[1],_RF[2],_RF[3],_f));return [0,E(_RI[1]),_RI[2]];})]);});},_Rt);});},_Ru=function(_RJ,_RK,_RL,_RM,_RN){return new F(function(){return A(_Rh,[_RJ,function(_RO,_RP,_RQ){return new F(function(){return A(_RK,[_f,_RP,new T(function(){var _RR=E(E(_RP)[2]),_RS=E(_RQ),_RT=E(_RS[1]),_RU=B(_wb(_RT[1],_RT[2],_RT[3],_RS[2],_RR[1],_RR[2],_RR[3],_f));return [0,E(_RU[1]),_RU[2]];})]);});},_RL,function(_RV,_RW,_RX){return new F(function(){return A(_RM,[_f,_RW,new T(function(){var _RY=E(E(_RW)[2]),_RZ=E(_RX),_S0=E(_RZ[1]),_S1=B(_wb(_S0[1],_S0[2],_S0[3],_RZ[2],_RY[1],_RY[2],_RY[3],_f));return [0,E(_S1[1]),_S1[2]];})]);});},function(_S2){return new F(function(){return A(_Rg,[_RJ,function(_S3,_S4,_S5){return new F(function(){return _Rn(_S3,_S4,_RK,_RL,function(_S6,_S7,_S8){return new F(function(){return A(_RK,[_S6,_S7,new T(function(){return B(_x0(_S5,_S8));})]);});},function(_S9){return new F(function(){return A(_RL,[new T(function(){return B(_x0(_S5,_S9));})]);});});});},_RL,function(_Sa,_Sb,_Sc){return new F(function(){return _Rn(_Sa,_Sb,_RK,_RL,function(_Sd,_Se,_Sf){return new F(function(){return A(_RM,[_Sd,_Se,new T(function(){var _Sg=E(_S2),_Sh=E(_Sg[1]),_Si=E(_Sc),_Sj=E(_Si[1]),_Sk=E(_Sf),_Sl=E(_Sk[1]),_Sm=B(_wb(_Sj[1],_Sj[2],_Sj[3],_Si[2],_Sl[1],_Sl[2],_Sl[3],_Sk[2])),_Sn=E(_Sm[1]),_So=B(_wb(_Sh[1],_Sh[2],_Sh[3],_Sg[2],_Sn[1],_Sn[2],_Sn[3],_Sm[2]));return [0,E(_So[1]),_So[2]];})]);});},function(_Sp){return new F(function(){return A(_RN,[new T(function(){var _Sq=E(_S2),_Sr=E(_Sq[1]),_Ss=E(_Sc),_St=E(_Ss[1]),_Su=E(_Sp),_Sv=E(_Su[1]),_Sw=B(_wb(_St[1],_St[2],_St[3],_Ss[2],_Sv[1],_Sv[2],_Sv[3],_Su[2])),_Sx=E(_Sw[1]),_Sy=B(_wb(_Sr[1],_Sr[2],_Sr[3],_Sq[2],_Sx[1],_Sx[2],_Sx[3],_Sw[2]));return [0,E(_Sy[1]),_Sy[2]];})]);});});});},function(_Sz){return new F(function(){return A(_RN,[new T(function(){return B(_x0(_S2,_Sz));})]);});}]);});}]);});};return new F(function(){return _Ru(_Ri,_Rj,_Rk,_Rl,_Rm);});},_SA=new T(function(){return B(unCStr("tab"));}),_SB=[1,_SA,_f],_SC=[0,9],_SD=function(_SE){return function(_SF,_SG,_SH,_SI,_SJ){return new F(function(){return _CL(new T(function(){return B(_D2(_SE,_SC));}),_SB,_SF,_SG,_SH,_SI,_SJ);});};},_SK=new T(function(){return B(_SD(_Ci));}),_SL=[0,39],_SM=[1,_SL,_f],_SN=new T(function(){return B(unCStr("\'\\\'\'"));}),_SO=function(_SP){var _SQ=E(E(_SP)[1]);return _SQ==39?E(_SN):[1,_SL,new T(function(){return B(_AY(_SQ,_SM));})];},_SR=function(_SS,_ST){return [1,_zp,new T(function(){return B(_Bf(_SS,[1,_zp,_ST]));})];},_SU=function(_SV){return new F(function(){return _1E(_SN,_SV);});},_SW=function(_SX,_SY){var _SZ=E(E(_SY)[1]);return _SZ==39?E(_SU):function(_T0){return [1,_SL,new T(function(){return B(_AY(_SZ,[1,_SL,_T0]));})];};},_T1=[0,_SW,_SO,_SR],_T2=function(_T3){return E(E(_T3)[2]);},_T4=function(_T5,_T6,_T7,_T8,_T9){var _Ta=new T(function(){return B(_T2(_T5));}),_Tb=function(_Tc){return new F(function(){return A(_T8,[_0,_T7,new T(function(){var _Td=E(E(_T7)[2]),_Te=E(_Tc),_Tf=E(_Te[1]),_Tg=B(_wb(_Tf[1],_Tf[2],_Tf[3],_Te[2],_Td[1],_Td[2],_Td[3],_f));return [0,E(_Tg[1]),_Tg[2]];})]);});};return new F(function(){return A(_T6,[_T7,function(_Th,_Ti,_Tj){return new F(function(){return A(_T9,[new T(function(){var _Tk=E(E(_Ti)[2]),_Tl=E(_Tj),_Tm=E(_Tl[1]),_Tn=B(_wb(_Tm[1],_Tm[2],_Tm[3],_Tl[2],_Tk[1],_Tk[2],_Tk[3],[1,new T(function(){return [1,E(B(A(_Ta,[_Th])))];}),_f]));return [0,E(_Tn[1]),_Tn[2]];})]);});},_Tb,function(_To,_Tp,_Tq){return new F(function(){return A(_T8,[_0,_T7,new T(function(){var _Tr=E(E(_T7)[2]),_Ts=E(E(_Tp)[2]),_Tt=E(_Tq),_Tu=E(_Tt[1]),_Tv=B(_wb(_Tu[1],_Tu[2],_Tu[3],_Tt[2],_Ts[1],_Ts[2],_Ts[3],[1,new T(function(){return [1,E(B(A(_Ta,[_To])))];}),_f])),_Tw=E(_Tv[1]),_Tx=B(_wb(_Tw[1],_Tw[2],_Tw[3],_Tv[2],_Tr[1],_Tr[2],_Tr[3],_f));return [0,E(_Tx[1]),_Tx[2]];})]);});},_Tb]);});},_Ty=function(_Tz,_TA,_TB,_TC){return new F(function(){return _T4(_T1,_SK,_TA,function(_TD,_TE,_TF){return new F(function(){return A(_TB,[_Tz,_TE,new T(function(){var _TG=E(E(_TE)[2]),_TH=E(_TF),_TI=E(_TH[1]),_TJ=B(_wb(_TI[1],_TI[2],_TI[3],_TH[2],_TG[1],_TG[2],_TG[3],_f));return [0,E(_TJ[1]),_TJ[2]];})]);});},_TC);});},_TK=function(_TL,_TM,_TN,_TO,_TP){return new F(function(){return A(_Dt,[_TL,function(_TQ,_TR,_TS){return new F(function(){return _Ty(_TQ,_TR,function(_TT,_TU,_TV){return new F(function(){return A(_TM,[_TT,_TU,new T(function(){return B(_x0(_TS,_TV));})]);});},function(_TW){return new F(function(){return A(_TN,[new T(function(){return B(_x0(_TS,_TW));})]);});});});},_TN,function(_TX,_TY,_TZ){return new F(function(){return _Ty(_TX,_TY,function(_U0,_U1,_U2){return new F(function(){return A(_TO,[_U0,_U1,new T(function(){return B(_x0(_TZ,_U2));})]);});},function(_U3){return new F(function(){return A(_TP,[new T(function(){return B(_x0(_TZ,_U3));})]);});});});},_TP]);});},_U4=[0,E(_f)],_U5=[1,_U4,_f],_U6=function(_U7,_U8,_U9,_Ua,_Ub,_Uc,_Ud){return new F(function(){return A(_U7,[new T(function(){return B(A(_U8,[_U9]));}),function(_Ue){var _Uf=E(_Ue);if(!_Uf[0]){return E(new T(function(){return B(A(_Ud,[[0,E(_Ua),_U5]]));}));}else{var _Ug=E(_Uf[1]);return new F(function(){return A(_Uc,[_Ug[1],[0,_Ug[2],E(_Ua),E(_Ub)],[0,E(_Ua),_f]]);});}}]);});},_Uh=new T(function(){return B(unCStr("end of input"));}),_Ui=[1,_Uh,_f],_Uj=function(_Uk,_Ul,_Um,_Un,_Uo,_Up,_Uq,_Ur){return new F(function(){return _CL(function(_Us,_Ut,_Uu,_Uv,_Uw){return new F(function(){return _T4(_Um,function(_Ux,_Uy,_Uz,_UA,_UB){var _UC=E(_Ux);return new F(function(){return _U6(_Uk,_Ul,_UC[1],_UC[2],_UC[3],_Uy,_UB);});},_Us,_Uv,_Uw);});},_Ui,_Un,_Uo,_Up,_Uq,_Ur);});},_UD=function(_UE,_UF,_UG,_UH,_UI,_UJ){return new F(function(){return _Uj(_zm,_C5,_T1,_UF,function(_UK,_UL,_UM){return new F(function(){return A(_UG,[_UE,_UL,new T(function(){var _UN=E(E(_UL)[2]),_UO=E(_UM),_UP=E(_UO[1]),_UQ=B(_wb(_UP[1],_UP[2],_UP[3],_UO[2],_UN[1],_UN[2],_UN[3],_f));return [0,E(_UQ[1]),_UQ[2]];})]);});},_UH,function(_UR,_US,_UT){return new F(function(){return A(_UI,[_UE,_US,new T(function(){var _UU=E(E(_US)[2]),_UV=E(_UT),_UW=E(_UV[1]),_UX=B(_wb(_UW[1],_UW[2],_UW[3],_UV[2],_UU[1],_UU[2],_UU[3],_f));return [0,E(_UX[1]),_UX[2]];})]);});},_UJ);});},_UY=function(_UZ,_V0,_V1,_V2,_V3){return new F(function(){return A(_Dt,[_UZ,function(_V4,_V5,_V6){return new F(function(){return _UD(_V4,_V5,_V0,_V1,function(_V7,_V8,_V9){return new F(function(){return A(_V0,[_V7,_V8,new T(function(){return B(_x0(_V6,_V9));})]);});},function(_Va){return new F(function(){return A(_V1,[new T(function(){return B(_x0(_V6,_Va));})]);});});});},_V1,function(_Vb,_Vc,_Vd){return new F(function(){return _UD(_Vb,_Vc,_V0,_V1,function(_Ve,_Vf,_Vg){return new F(function(){return A(_V2,[_Ve,_Vf,new T(function(){return B(_x0(_Vd,_Vg));})]);});},function(_Vh){return new F(function(){return A(_V3,[new T(function(){return B(_x0(_Vd,_Vh));})]);});});});},_V3]);});},_Vi=function(_Vj,_Vk,_Vl,_Vm){var _Vn=function(_Vo){var _Vp=function(_Vq){return new F(function(){return A(_Vm,[new T(function(){return B(_x0(_Vo,_Vq));})]);});};return new F(function(){return _TK(_Vj,_Vk,_Vp,function(_Vr,_Vs,_Vt){return new F(function(){return A(_Vl,[_Vr,_Vs,new T(function(){return B(_x0(_Vo,_Vt));})]);});},_Vp);});};return new F(function(){return _UY(_Vj,_Vk,_Vn,_Vl,_Vn);});},_Vu=function(_Vv,_Vw,_Vx,_Vy,_Vz){return new F(function(){return _Vi(_Vv,_Vw,_Vy,_Vz);});},_VA=function(_VB){return true;},_VC=function(_VD,_VE,_VF,_VG,_VH){var _VI=E(_VD),_VJ=E(_VI[2]);return new F(function(){return _Bl(_zm,_C5,_VA,_VI[1],_VJ[1],_VJ[2],_VJ[3],_VI[3],_VE,_VH);});},_VK=function(_VL,_VM,_VN,_VO,_VP){return new F(function(){return A(_SK,[_VL,function(_VQ,_VR,_VS){return new F(function(){return _Rf(_VC,_Vu,_VR,_VM,_VN,function(_VT,_VU,_VV){return new F(function(){return A(_VM,[_VT,_VU,new T(function(){return B(_x0(_VS,_VV));})]);});},function(_VW){return new F(function(){return A(_VN,[new T(function(){return B(_x0(_VS,_VW));})]);});});});},_VN,function(_VX,_VY,_VZ){return new F(function(){return _Rf(_VC,_Vu,_VY,_VM,_VN,function(_W0,_W1,_W2){return new F(function(){return A(_VO,[_W0,_W1,new T(function(){return B(_x0(_VZ,_W2));})]);});},function(_W3){return new F(function(){return A(_VP,[new T(function(){return B(_x0(_VZ,_W3));})]);});});});},_VP]);});},_W4=[0,_Q4,_f],_W5=[0,_f,1,1],_W6=function(_W7){return E(_W7);},_W8=new T(function(){return B(_ik("ww_sboG{v} [lid] forall a{tv i3Iw} [tv].\n                 base:GHC.Base.String{tc 36u} -> m{tv a8Yp} [tv] a{tv i3Iw} [tv]"));}),_W9=new T(function(){return B(_ik("ww_sboE{v} [lid] forall a{tv i3It} [tv] b{tv i3Iu} [tv].\n                 m{tv a8Yp} [tv] a{tv i3It} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]\n                 -> m{tv a8Yp} [tv] b{tv i3Iu} [tv]"));}),_Wa=[0,_zm,_W9,_W6,_W8],_Wb=[0,10],_Wc=[1,_Wb,_f],_Wd=function(_We){return new F(function(){return unAppCStr("string error",new T(function(){var _Wf=E(_We),_Wg=E(_Wf[1]);return B(_1E(B(_9N(_Wg[1],_Wg[2],_Wg[3],_Wf[2])),_Wc));}));});},_Wh=function(_Wi,_Wj,_Wk,_Wl,_Wm){return new F(function(){return A(_SK,[_Wj,function(_Wn,_Wo,_Wp){return new F(function(){return A(_Wk,[_Wi,_Wo,new T(function(){var _Wq=E(E(_Wo)[2]),_Wr=E(_Wp),_Ws=E(_Wr[1]),_Wt=B(_wb(_Ws[1],_Ws[2],_Ws[3],_Wr[2],_Wq[1],_Wq[2],_Wq[3],_f));return [0,E(_Wt[1]),_Wt[2]];})]);});},_Wm,function(_Wu,_Wv,_Ww){return new F(function(){return A(_Wl,[_Wi,_Wv,new T(function(){var _Wx=E(E(_Wv)[2]),_Wy=E(_Ww),_Wz=E(_Wy[1]),_WA=B(_wb(_Wz[1],_Wz[2],_Wz[3],_Wy[2],_Wx[1],_Wx[2],_Wx[3],_f));return [0,E(_WA[1]),_WA[2]];})]);});},_Wm]);});},_WB=function(_WC,_WD,_WE,_WF,_WG){return new F(function(){return A(_Dt,[_WC,function(_WH,_WI,_WJ){return new F(function(){return _Wh(_WH,_WI,_WD,function(_WK,_WL,_WM){return new F(function(){return A(_WD,[_WK,_WL,new T(function(){return B(_x0(_WJ,_WM));})]);});},function(_WN){return new F(function(){return A(_WE,[new T(function(){return B(_x0(_WJ,_WN));})]);});});});},_WE,function(_WO,_WP,_WQ){return new F(function(){return _Wh(_WO,_WP,_WD,function(_WR,_WS,_WT){return new F(function(){return A(_WF,[_WR,_WS,new T(function(){return B(_x0(_WQ,_WT));})]);});},function(_WU){return new F(function(){return A(_WG,[new T(function(){return B(_x0(_WQ,_WU));})]);});});});},_WG]);});},_WV=function(_WW,_WX,_WY,_WZ,_X0){return new F(function(){return _WB(_WW,_WX,_WY,_WZ,function(_X1){var _X2=E(_WW),_X3=E(_X2[2]),_X4=E(_X2[1]);return _X4[0]==0?B(A(_X0,[new T(function(){var _X5=E(_X1),_X6=E(_X5[1]),_X7=B(_wb(_X6[1],_X6[2],_X6[3],_X5[2],_X3[1],_X3[2],_X3[3],_U5));return [0,E(_X7[1]),_X7[2]];})])):B(A(_WX,[_X4[1],[0,_X4[2],E(_X3),E(_X2[3])],[0,E(_X3),_f]]));});});},_X8=function(_X9,_Xa,_Xb,_Xc,_Xd){return new F(function(){return _wy(_WV,_X9,_Xa,_Xb,_Xc);});},_Xe=function(_Xf,_Xg,_Xh){return [0,_Xf,E(E(_Xg)),_Xh];},_Xi=function(_Xj,_Xk,_Xl){var _Xm=new T(function(){return B(_BZ(_Xj));}),_Xn=new T(function(){return B(_BZ(_Xj));});return new F(function(){return A(_Xk,[_Xl,function(_Xo,_Xp,_Xq){return new F(function(){return A(_Xm,[[0,new T(function(){return B(A(_Xn,[new T(function(){return B(_Xe(_Xo,_Xp,_Xq));})]));})]]);});},function(_Xr){return new F(function(){return A(_Xm,[[0,new T(function(){return B(A(_Xn,[[1,_Xr]]));})]]);});},function(_Xs,_Xt,_Xu){return new F(function(){return A(_Xm,[new T(function(){return [1,E(B(A(_Xn,[new T(function(){return B(_Xe(_Xs,_Xt,_Xu));})])))];})]);});},function(_Xv){return new F(function(){return A(_Xm,[new T(function(){return [1,E(B(A(_Xn,[[1,_Xv]])))];})]);});}]);});},_Xw=function(_Xx){return function(_Xy,_Xz,_XA,_XB,_XC){return new F(function(){return A(_XB,[new T(function(){var _XD=B(_Xi(_Wa,_XE,[0,new T(function(){var _XF=B(_Xi(_Wa,_X8,[0,_Xx,E(_W5),E(_0)]));if(!_XF[0]){var _XG=E(_XF[1]),_XH=_XG[0]==0?B(_1E(_XG[1],_Wc)):B(_Wd(_XG[1]));}else{var _XI=E(_XF[1]),_XH=_XI[0]==0?B(_1E(_XI[1],_Wc)):B(_Wd(_XI[1]));}return _XH;}),E(_W5),E(_0)]));if(!_XD[0]){var _XJ=E(_XD[1]),_XK=_XJ[0]==0?E(_XJ[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9S(_XJ[1]));})));})],_f],_f],_W4];}else{var _XL=E(_XD[1]),_XK=_XL[0]==0?E(_XL[1]):[0,[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9S(_XL[1]));})));})],_f],_f],_W4];}return _XK;}),_Xy,new T(function(){return [0,E(E(_Xy)[2]),_f];})]);});};},_XM=function(_XN,_XO,_XP,_XQ,_XR){return new F(function(){return _VK(_XN,function(_XS,_XT,_XU){return new F(function(){return A(_Xw,[_XS,_XT,_XO,_XP,function(_XV,_XW,_XX){return new F(function(){return A(_XO,[_XV,_XW,new T(function(){return B(_x0(_XU,_XX));})]);});},function(_XY){return new F(function(){return A(_XP,[new T(function(){return B(_x0(_XU,_XY));})]);});}]);});},_XP,function(_XZ,_Y0,_Y1){return new F(function(){return A(_Xw,[_XZ,_Y0,_XO,_XP,function(_Y2,_Y3,_Y4){return new F(function(){return A(_XQ,[_Y2,_Y3,new T(function(){return B(_x0(_Y1,_Y4));})]);});},function(_Y5){return new F(function(){return A(_XR,[new T(function(){return B(_x0(_Y1,_Y5));})]);});}]);});},_XR);});},_Y6=function(_Y7,_Y8,_Y9,_Ya,_Yb,_Yc){var _Yd=function(_Ye,_Yf,_Yg,_Yh,_Yi){var _Yj=function(_Yk,_Yl,_Ym,_Yn,_Yo){return new F(function(){return A(_Yh,[[0,[1,[0,_Y7,_Yl,_Ym]],_Yk],_Yn,new T(function(){var _Yp=E(_Yo),_Yq=E(_Yp[1]),_Yr=E(E(_Yn)[2]),_Ys=B(_wb(_Yq[1],_Yq[2],_Yq[3],_Yp[2],_Yr[1],_Yr[2],_Yr[3],_f));return [0,E(_Ys[1]),_Ys[2]];})]);});},_Yt=function(_Yu){return new F(function(){return _Yj(_f,_Q4,_f,_Ye,new T(function(){var _Yv=E(E(_Ye)[2]),_Yw=E(_Yu),_Yx=E(_Yw[1]),_Yy=B(_wb(_Yx[1],_Yx[2],_Yx[3],_Yw[2],_Yv[1],_Yv[2],_Yv[3],_f));return [0,E(_Yy[1]),_Yy[2]];}));});};return new F(function(){return _XM(_Ye,function(_Yz,_YA,_YB){var _YC=E(_Yz),_YD=E(_YC[2]);return new F(function(){return A(_Yf,[[0,[1,[0,_Y7,_YD[1],_YD[2]]],_YC[1]],_YA,new T(function(){var _YE=E(_YB),_YF=E(_YE[1]),_YG=E(E(_YA)[2]),_YH=B(_wb(_YF[1],_YF[2],_YF[3],_YE[2],_YG[1],_YG[2],_YG[3],_f));return [0,E(_YH[1]),_YH[2]];})]);});},_Yt,function(_YI,_YJ,_YK){var _YL=E(_YI),_YM=E(_YL[2]);return new F(function(){return _Yj(_YL[1],_YM[1],_YM[2],_YJ,_YK);});},_Yt);});};return new F(function(){return A(_Dt,[_Y8,function(_YN,_YO,_YP){return new F(function(){return _Yd(_YO,_Y9,_Ya,function(_YQ,_YR,_YS){return new F(function(){return A(_Y9,[_YQ,_YR,new T(function(){return B(_x0(_YP,_YS));})]);});},function(_YT){return new F(function(){return A(_Ya,[new T(function(){return B(_x0(_YP,_YT));})]);});});});},_Yc,function(_YU,_YV,_YW){return new F(function(){return _Yd(_YV,_Y9,_Ya,function(_YX,_YY,_YZ){return new F(function(){return A(_Yb,[_YX,_YY,new T(function(){return B(_x0(_YW,_YZ));})]);});},function(_Z0){return new F(function(){return A(_Yc,[new T(function(){return B(_x0(_YW,_Z0));})]);});});});},_Yc]);});},_Z1=new T(function(){return B(unCStr(" associative operator"));}),_Z2=function(_Z3,_Z4){var _Z5=[1,new T(function(){return [3,E(B(unAppCStr("ambiguous use of a ",new T(function(){return B(_1E(_Z3,_Z1));}))))];}),_f];return function(_Z6,_Z7,_Z8,_Z9,_Za){return new F(function(){return A(_Z4,[_Z6,function(_Zb,_Zc,_Zd){return new F(function(){return A(_Za,[new T(function(){var _Ze=E(E(_Zc)[2]),_Zf=E(_Zd),_Zg=E(_Zf[1]),_Zh=B(_wb(_Zg[1],_Zg[2],_Zg[3],_Zf[2],_Ze[1],_Ze[2],_Ze[3],_Z5));return [0,E(_Zh[1]),_Zh[2]];})]);});},_Za,function(_Zi,_Zj,_Zk){return new F(function(){return A(_Za,[new T(function(){var _Zl=E(E(_Zj)[2]),_Zm=E(_Zk),_Zn=E(_Zm[1]),_Zo=B(_wb(_Zn[1],_Zn[2],_Zn[3],_Zm[2],_Zl[1],_Zl[2],_Zl[3],_Z5));return [0,E(_Zo[1]),_Zo[2]];})]);});},_Za]);});};},_Zp=function(_Zq,_Zr,_Zs,_Zt,_Zu,_Zv){var _Zw=E(_Zq);if(!_Zw[0]){return new F(function(){return A(_Zv,[new T(function(){return [0,E(E(_Zr)[2]),_f];})]);});}else{return new F(function(){return A(_Zw[1],[_Zr,_Zs,_Zt,_Zu,function(_Zx){return new F(function(){return _Zp(_Zw[2],_Zr,_Zs,_Zt,function(_Zy,_Zz,_ZA){return new F(function(){return A(_Zu,[_Zy,_Zz,new T(function(){return B(_x0(_Zx,_ZA));})]);});},function(_ZB){return new F(function(){return A(_Zv,[new T(function(){return B(_x0(_Zx,_ZB));})]);});});});}]);});}},_ZC=new T(function(){return B(unCStr("right"));}),_ZD=new T(function(){return B(unCStr("left"));}),_ZE=new T(function(){return B(unCStr("non"));}),_ZF=new T(function(){return B(unCStr("operator"));}),_ZG=[1,_ZF,_f],_ZH=[1,_f,_f],_ZI=function(_ZJ){var _ZK=E(_ZJ);if(!_ZK[0]){return [0,_f,_f,_f,_f,_f];}else{var _ZL=_ZK[2],_ZM=E(_ZK[1]);switch(_ZM[0]){case 0:var _ZN=_ZM[1],_ZO=B(_ZI(_ZL)),_ZP=_ZO[1],_ZQ=_ZO[2],_ZR=_ZO[3],_ZS=_ZO[4],_ZT=_ZO[5];switch(E(_ZM[2])){case 0:return [0,_ZP,_ZQ,[1,_ZN,_ZR],_ZS,_ZT];case 1:return [0,_ZP,[1,_ZN,_ZQ],_ZR,_ZS,_ZT];default:return [0,[1,_ZN,_ZP],_ZQ,_ZR,_ZS,_ZT];}break;case 1:var _ZU=B(_ZI(_ZL));return [0,_ZU[1],_ZU[2],_ZU[3],[1,_ZM[1],_ZU[4]],_ZU[5]];default:var _ZV=B(_ZI(_ZL));return [0,_ZV[1],_ZV[2],_ZV[3],_ZV[4],[1,_ZM[1],_ZV[5]]];}}},_ZW=function(_ZX,_ZY){while(1){var _ZZ=(function(_100,_101){var _102=E(_101);if(!_102[0]){return E(_100);}else{var _103=new T(function(){var _104=B(_ZI(_102[1]));return [0,_104[1],_104[2],_104[3],_104[4],_104[5]];}),_105=new T(function(){return E(E(_103)[2]);}),_106=new T(function(){return B(_Z2(_ZD,function(_107,_108,_109,_10a,_10b){return new F(function(){return _Zp(_105,_107,_108,_109,_10a,_10b);});}));}),_10c=new T(function(){return E(E(_103)[1]);}),_10d=new T(function(){return E(E(_103)[3]);}),_10e=new T(function(){return B(_Z2(_ZE,function(_10f,_10g,_10h,_10i,_10j){return new F(function(){return _Zp(_10d,_10f,_10g,_10h,_10i,_10j);});}));}),_10k=function(_10l,_10m,_10n,_10o,_10p,_10q){var _10r=function(_10s,_10t,_10u,_10v,_10w){var _10x=new T(function(){return B(A(_10l,[_10s]));});return new F(function(){return _Zp(new T(function(){return E(E(_103)[5]);}),_10t,function(_10y,_10z,_10A){return new F(function(){return A(_10u,[new T(function(){return B(A(_10y,[_10x]));}),_10z,new T(function(){var _10B=E(E(_10z)[2]),_10C=E(_10A),_10D=E(_10C[1]),_10E=B(_wb(_10D[1],_10D[2],_10D[3],_10C[2],_10B[1],_10B[2],_10B[3],_f));return [0,E(_10E[1]),_10E[2]];})]);});},_10v,function(_10F,_10G,_10H){return new F(function(){return A(_10w,[new T(function(){return B(A(_10F,[_10x]));}),_10G,new T(function(){var _10I=E(E(_10G)[2]),_10J=_10I[1],_10K=_10I[2],_10L=_10I[3],_10M=E(_10H),_10N=E(_10M[1]),_10O=_10N[2],_10P=_10N[3],_10Q=E(_10M[2]);if(!_10Q[0]){switch(B(_w3(_10N[1],_10J))){case 0:var _10R=[0,E(_10I),_f];break;case 1:if(_10O>=_10K){if(_10O!=_10K){var _10S=[0,E(_10N),_f];}else{if(_10P>=_10L){var _10T=_10P!=_10L?[0,E(_10N),_f]:[0,E(_10N),_wa];}else{var _10T=[0,E(_10I),_f];}var _10U=_10T,_10S=_10U;}var _10V=_10S,_10W=_10V;}else{var _10W=[0,E(_10I),_f];}var _10X=_10W,_10R=_10X;break;default:var _10R=[0,E(_10N),_f];}var _10Y=_10R;}else{var _10Z=B(_Cq(_10N,_10Q,_ZH)),_110=E(_10Z[1]),_111=B(_wb(_110[1],_110[2],_110[3],_10Z[2],_10J,_10K,_10L,_f)),_10Y=[0,E(_111[1]),_111[2]];}var _112=_10Y,_113=_112,_114=_113,_115=_114;return _115;})]);});},function(_116){return new F(function(){return A(_10w,[_10x,_10t,new T(function(){var _117=E(E(_10t)[2]),_118=_117[1],_119=_117[2],_11a=_117[3],_11b=E(_116),_11c=B(_Cq(_11b[1],_11b[2],_ZH)),_11d=E(_11c[1]),_11e=B(_wb(_11d[1],_11d[2],_11d[3],_11c[2],_118,_119,_11a,_f)),_11f=E(_11e[1]),_11g=B(_wb(_11f[1],_11f[2],_11f[3],_11e[2],_118,_119,_11a,_f));return [0,E(_11g[1]),_11g[2]];})]);});});});};return new F(function(){return A(_100,[_10m,function(_11h,_11i,_11j){return new F(function(){return _10r(_11h,_11i,_10n,_10o,function(_11k,_11l,_11m){return new F(function(){return A(_10n,[_11k,_11l,new T(function(){return B(_x0(_11j,_11m));})]);});});});},_10o,function(_11n,_11o,_11p){return new F(function(){return _10r(_11n,_11o,_10n,_10o,function(_11q,_11r,_11s){return new F(function(){return A(_10p,[_11q,_11r,new T(function(){return B(_x0(_11p,_11s));})]);});});});},_10q]);});},_11t=function(_11u,_11v,_11w,_11x,_11y){var _11z=function(_11A,_11B,_11C){return new F(function(){return _10k(_11A,_11B,_11v,_11w,function(_11D,_11E,_11F){return new F(function(){return A(_11x,[_11D,_11E,new T(function(){return B(_x0(_11C,_11F));})]);});},function(_11G){return new F(function(){return A(_11y,[new T(function(){return B(_x0(_11C,_11G));})]);});});});};return new F(function(){return _Zp(new T(function(){return E(E(_103)[4]);}),_11u,function(_11H,_11I,_11J){return new F(function(){return _10k(_11H,_11I,_11v,_11w,function(_11K,_11L,_11M){return new F(function(){return A(_11v,[_11K,_11L,new T(function(){return B(_x0(_11J,_11M));})]);});},function(_11N){return new F(function(){return A(_11w,[new T(function(){return B(_x0(_11J,_11N));})]);});});});},_11w,function(_11O,_11P,_11Q){return new F(function(){return _11z(_11O,_11P,new T(function(){var _11R=E(_11Q),_11S=E(_11R[2]);if(!_11S[0]){var _11T=E(_11R);}else{var _11U=B(_Cq(_11R[1],_11S,_ZH)),_11T=[0,E(_11U[1]),_11U[2]];}var _11V=_11T;return _11V;}));});},function(_11W){return new F(function(){return _11z(_4r,_11u,new T(function(){var _11X=E(E(_11u)[2]),_11Y=E(_11W),_11Z=B(_Cq(_11Y[1],_11Y[2],_ZH)),_120=E(_11Z[1]),_121=B(_wb(_120[1],_120[2],_120[3],_11Z[2],_11X[1],_11X[2],_11X[3],_f));return [0,E(_121[1]),_121[2]];}));});});});},_122=function(_123,_124,_125,_126,_127,_128){var _129=function(_12a){return new F(function(){return A(_106,[_124,_125,_126,function(_12b,_12c,_12d){return new F(function(){return A(_127,[_12b,_12c,new T(function(){return B(_x0(_12a,_12d));})]);});},function(_12e){return new F(function(){return A(_10e,[_124,_125,_126,function(_12f,_12g,_12h){return new F(function(){return A(_127,[_12f,_12g,new T(function(){var _12i=E(_12a),_12j=E(_12i[1]),_12k=E(_12e),_12l=E(_12k[1]),_12m=E(_12h),_12n=E(_12m[1]),_12o=B(_wb(_12l[1],_12l[2],_12l[3],_12k[2],_12n[1],_12n[2],_12n[3],_12m[2])),_12p=E(_12o[1]),_12q=B(_wb(_12j[1],_12j[2],_12j[3],_12i[2],_12p[1],_12p[2],_12p[3],_12o[2]));return [0,E(_12q[1]),_12q[2]];})]);});},function(_12r){return new F(function(){return A(_128,[new T(function(){var _12s=E(_12a),_12t=E(_12s[1]),_12u=E(_12e),_12v=E(_12u[1]),_12w=E(_12r),_12x=E(_12w[1]),_12y=B(_wb(_12v[1],_12v[2],_12v[3],_12u[2],_12x[1],_12x[2],_12x[3],_12w[2])),_12z=E(_12y[1]),_12A=B(_wb(_12t[1],_12t[2],_12t[3],_12s[2],_12z[1],_12z[2],_12z[3],_12y[2]));return [0,E(_12A[1]),_12A[2]];})]);});}]);});}]);});},_12B=function(_12C,_12D,_12E,_12F,_12G,_12H){var _12I=function(_12J,_12K,_12L){return new F(function(){return A(_12E,[new T(function(){return B(A(_12C,[_123,_12J]));}),_12K,new T(function(){var _12M=E(E(_12K)[2]),_12N=E(_12L),_12O=E(_12N[1]),_12P=B(_wb(_12O[1],_12O[2],_12O[3],_12N[2],_12M[1],_12M[2],_12M[3],_f));return [0,E(_12P[1]),_12P[2]];})]);});};return new F(function(){return _11t(_12D,function(_12Q,_12R,_12S){return new F(function(){return _122(_12Q,_12R,_12I,_12F,function(_12T,_12U,_12V){return new F(function(){return _12I(_12T,_12U,new T(function(){var _12W=E(_12S),_12X=E(_12W[1]),_12Y=E(_12V),_12Z=E(_12Y[1]),_130=B(_wb(_12X[1],_12X[2],_12X[3],_12W[2],_12Z[1],_12Z[2],_12Z[3],_12Y[2]));return [0,E(_130[1]),_130[2]];},1));});},function(_131){return new F(function(){return _12I(_12Q,_12R,new T(function(){var _132=E(E(_12R)[2]),_133=E(_12S),_134=E(_133[1]),_135=E(_131),_136=E(_135[1]),_137=B(_wb(_136[1],_136[2],_136[3],_135[2],_132[1],_132[2],_132[3],_f)),_138=E(_137[1]),_139=B(_wb(_134[1],_134[2],_134[3],_133[2],_138[1],_138[2],_138[3],_137[2]));return [0,E(_139[1]),_139[2]];},1));});});});},_12F,function(_13a,_13b,_13c){var _13d=function(_13e,_13f,_13g){return new F(function(){return A(_12G,[new T(function(){return B(A(_12C,[_123,_13e]));}),_13f,new T(function(){var _13h=E(E(_13f)[2]),_13i=E(_13c),_13j=E(_13i[1]),_13k=E(_13g),_13l=E(_13k[1]),_13m=B(_wb(_13j[1],_13j[2],_13j[3],_13i[2],_13l[1],_13l[2],_13l[3],_13k[2])),_13n=E(_13m[1]),_13o=B(_wb(_13n[1],_13n[2],_13n[3],_13m[2],_13h[1],_13h[2],_13h[3],_f));return [0,E(_13o[1]),_13o[2]];})]);});};return new F(function(){return _122(_13a,_13b,_12I,_12F,_13d,function(_13p){return new F(function(){return _13d(_13a,_13b,new T(function(){var _13q=E(E(_13b)[2]),_13r=E(_13p),_13s=E(_13r[1]),_13t=B(_wb(_13s[1],_13s[2],_13s[3],_13r[2],_13q[1],_13q[2],_13q[3],_f));return [0,E(_13t[1]),_13t[2]];},1));});});});},_12H);});};return new F(function(){return _Zp(_10c,_124,function(_13u,_13v,_13w){return new F(function(){return _12B(_13u,_13v,_125,_126,function(_13x,_13y,_13z){return new F(function(){return A(_125,[_13x,_13y,new T(function(){return B(_x0(_13w,_13z));})]);});},function(_13A){return new F(function(){return A(_126,[new T(function(){return B(_x0(_13w,_13A));})]);});});});},_126,function(_13B,_13C,_13D){return new F(function(){return _12B(_13B,_13C,_125,_126,function(_13E,_13F,_13G){return new F(function(){return A(_127,[_13E,_13F,new T(function(){return B(_x0(_13D,_13G));})]);});},function(_13H){return new F(function(){return _129(new T(function(){return B(_x0(_13D,_13H));}));});});});},_129);});},_13I=new T(function(){return B(_Z2(_ZC,function(_13J,_13K,_13L,_13M,_13N){return new F(function(){return _Zp(_10c,_13J,_13K,_13L,_13M,_13N);});}));}),_13O=function(_13P,_13Q,_13R,_13S,_13T,_13U){var _13V=function(_13W){return new F(function(){return A(_13I,[_13Q,_13R,_13S,function(_13X,_13Y,_13Z){return new F(function(){return A(_13T,[_13X,_13Y,new T(function(){return B(_x0(_13W,_13Z));})]);});},function(_140){return new F(function(){return A(_10e,[_13Q,_13R,_13S,function(_141,_142,_143){return new F(function(){return A(_13T,[_141,_142,new T(function(){var _144=E(_13W),_145=E(_144[1]),_146=E(_140),_147=E(_146[1]),_148=E(_143),_149=E(_148[1]),_14a=B(_wb(_147[1],_147[2],_147[3],_146[2],_149[1],_149[2],_149[3],_148[2])),_14b=E(_14a[1]),_14c=B(_wb(_145[1],_145[2],_145[3],_144[2],_14b[1],_14b[2],_14b[3],_14a[2]));return [0,E(_14c[1]),_14c[2]];})]);});},function(_14d){return new F(function(){return A(_13U,[new T(function(){var _14e=E(_13W),_14f=E(_14e[1]),_14g=E(_140),_14h=E(_14g[1]),_14i=E(_14d),_14j=E(_14i[1]),_14k=B(_wb(_14h[1],_14h[2],_14h[3],_14g[2],_14j[1],_14j[2],_14j[3],_14i[2])),_14l=E(_14k[1]),_14m=B(_wb(_14f[1],_14f[2],_14f[3],_14e[2],_14l[1],_14l[2],_14l[3],_14k[2]));return [0,E(_14m[1]),_14m[2]];})]);});}]);});}]);});},_14n=function(_14o,_14p,_14q,_14r,_14s,_14t){var _14u=function(_14v){var _14w=new T(function(){return B(A(_14o,[_13P,_14v]));});return function(_14x,_14y,_14z,_14A,_14B){return new F(function(){return _13O(_14w,_14x,_14y,_14z,_14A,function(_14C){return new F(function(){return A(_14A,[_14w,_14x,new T(function(){var _14D=E(E(_14x)[2]),_14E=E(_14C),_14F=E(_14E[1]),_14G=B(_wb(_14F[1],_14F[2],_14F[3],_14E[2],_14D[1],_14D[2],_14D[3],_f));return [0,E(_14G[1]),_14G[2]];})]);});});});};};return new F(function(){return _11t(_14p,function(_14H,_14I,_14J){return new F(function(){return A(_14u,[_14H,_14I,_14q,_14r,function(_14K,_14L,_14M){return new F(function(){return A(_14q,[_14K,_14L,new T(function(){return B(_x0(_14J,_14M));})]);});},function(_14N){return new F(function(){return A(_14r,[new T(function(){return B(_x0(_14J,_14N));})]);});}]);});},_14r,function(_14O,_14P,_14Q){return new F(function(){return A(_14u,[_14O,_14P,_14q,_14r,function(_14R,_14S,_14T){return new F(function(){return A(_14s,[_14R,_14S,new T(function(){return B(_x0(_14Q,_14T));})]);});},function(_14U){return new F(function(){return A(_14t,[new T(function(){return B(_x0(_14Q,_14U));})]);});}]);});},_14t);});};return new F(function(){return _Zp(_105,_13Q,function(_14V,_14W,_14X){return new F(function(){return _14n(_14V,_14W,_13R,_13S,function(_14Y,_14Z,_150){return new F(function(){return A(_13R,[_14Y,_14Z,new T(function(){return B(_x0(_14X,_150));})]);});},function(_151){return new F(function(){return A(_13S,[new T(function(){return B(_x0(_14X,_151));})]);});});});},_13S,function(_152,_153,_154){return new F(function(){return _14n(_152,_153,_13R,_13S,function(_155,_156,_157){return new F(function(){return A(_13T,[_155,_156,new T(function(){return B(_x0(_154,_157));})]);});},function(_158){return new F(function(){return _13V(new T(function(){return B(_x0(_154,_158));}));});});});},_13V);});},_159=function(_15a,_15b,_15c,_15d,_15e,_15f){var _15g=function(_15h,_15i,_15j,_15k,_15l,_15m){var _15n=function(_15o){return function(_15p,_15q,_15r,_15s,_15t){return new F(function(){return A(_13I,[_15p,_15q,_15r,_15s,function(_15u){return new F(function(){return A(_106,[_15p,_15q,_15r,function(_15v,_15w,_15x){return new F(function(){return A(_15s,[_15v,_15w,new T(function(){return B(_x0(_15u,_15x));})]);});},function(_15y){return new F(function(){return A(_10e,[_15p,_15q,_15r,function(_15z,_15A,_15B){return new F(function(){return A(_15s,[_15z,_15A,new T(function(){var _15C=E(_15u),_15D=E(_15C[1]),_15E=E(_15y),_15F=E(_15E[1]),_15G=E(_15B),_15H=E(_15G[1]),_15I=B(_wb(_15F[1],_15F[2],_15F[3],_15E[2],_15H[1],_15H[2],_15H[3],_15G[2])),_15J=E(_15I[1]),_15K=B(_wb(_15D[1],_15D[2],_15D[3],_15C[2],_15J[1],_15J[2],_15J[3],_15I[2]));return [0,E(_15K[1]),_15K[2]];})]);});},function(_15L){return new F(function(){return A(_15s,[new T(function(){return B(A(_15h,[_15a,_15o]));}),_15p,new T(function(){var _15M=E(E(_15p)[2]),_15N=E(_15u),_15O=E(_15N[1]),_15P=E(_15y),_15Q=E(_15P[1]),_15R=E(_15L),_15S=E(_15R[1]),_15T=B(_wb(_15S[1],_15S[2],_15S[3],_15R[2],_15M[1],_15M[2],_15M[3],_f)),_15U=E(_15T[1]),_15V=B(_wb(_15Q[1],_15Q[2],_15Q[3],_15P[2],_15U[1],_15U[2],_15U[3],_15T[2])),_15W=E(_15V[1]),_15X=B(_wb(_15O[1],_15O[2],_15O[3],_15N[2],_15W[1],_15W[2],_15W[3],_15V[2]));return [0,E(_15X[1]),_15X[2]];})]);});}]);});}]);});}]);});};};return new F(function(){return _11t(_15i,function(_15Y,_15Z,_160){return new F(function(){return A(_15n,[_15Y,_15Z,_15j,_15k,function(_161,_162,_163){return new F(function(){return A(_15j,[_161,_162,new T(function(){return B(_x0(_160,_163));})]);});},function(_164){return new F(function(){return A(_15k,[new T(function(){return B(_x0(_160,_164));})]);});}]);});},_15k,function(_165,_166,_167){return new F(function(){return A(_15n,[_165,_166,_15j,_15k,function(_168,_169,_16a){return new F(function(){return A(_15l,[_168,_169,new T(function(){return B(_x0(_167,_16a));})]);});},function(_16b){return new F(function(){return A(_15m,[new T(function(){return B(_x0(_167,_16b));})]);});}]);});},_15m);});};return new F(function(){return _CL(function(_16c,_16d,_16e,_16f,_16g){return new F(function(){return _122(_15a,_16c,_16d,_16e,_16f,function(_16h){return new F(function(){return _13O(_15a,_16c,_16d,_16e,function(_16i,_16j,_16k){return new F(function(){return A(_16f,[_16i,_16j,new T(function(){return B(_x0(_16h,_16k));})]);});},function(_16l){var _16m=function(_16n){return new F(function(){return A(_16f,[_15a,_16c,new T(function(){var _16o=E(E(_16c)[2]),_16p=E(_16h),_16q=E(_16p[1]),_16r=E(_16l),_16s=E(_16r[1]),_16t=E(_16n),_16u=E(_16t[1]),_16v=B(_wb(_16u[1],_16u[2],_16u[3],_16t[2],_16o[1],_16o[2],_16o[3],_f)),_16w=E(_16v[1]),_16x=B(_wb(_16s[1],_16s[2],_16s[3],_16r[2],_16w[1],_16w[2],_16w[3],_16v[2])),_16y=E(_16x[1]),_16z=B(_wb(_16q[1],_16q[2],_16q[3],_16p[2],_16y[1],_16y[2],_16y[3],_16x[2]));return [0,E(_16z[1]),_16z[2]];})]);});};return new F(function(){return _Zp(_10d,_16c,function(_16A,_16B,_16C){return new F(function(){return _15g(_16A,_16B,_16d,_16e,function(_16D,_16E,_16F){return new F(function(){return A(_16d,[_16D,_16E,new T(function(){return B(_x0(_16C,_16F));})]);});},function(_16G){return new F(function(){return A(_16e,[new T(function(){return B(_x0(_16C,_16G));})]);});});});},_16e,function(_16H,_16I,_16J){return new F(function(){return _15g(_16H,_16I,_16d,_16e,function(_16K,_16L,_16M){return new F(function(){return A(_16f,[_16K,_16L,new T(function(){var _16N=E(_16h),_16O=E(_16N[1]),_16P=E(_16l),_16Q=E(_16P[1]),_16R=E(_16J),_16S=E(_16R[1]),_16T=E(_16M),_16U=E(_16T[1]),_16V=B(_wb(_16S[1],_16S[2],_16S[3],_16R[2],_16U[1],_16U[2],_16U[3],_16T[2])),_16W=E(_16V[1]),_16X=B(_wb(_16Q[1],_16Q[2],_16Q[3],_16P[2],_16W[1],_16W[2],_16W[3],_16V[2])),_16Y=E(_16X[1]),_16Z=B(_wb(_16O[1],_16O[2],_16O[3],_16N[2],_16Y[1],_16Y[2],_16Y[3],_16X[2]));return [0,E(_16Z[1]),_16Z[2]];})]);});},function(_170){return new F(function(){return _16m(new T(function(){var _171=E(_16J),_172=E(_171[1]),_173=E(_170),_174=E(_173[1]),_175=B(_wb(_172[1],_172[2],_172[3],_171[2],_174[1],_174[2],_174[3],_173[2]));return [0,E(_175[1]),_175[2]];},1));});});});},_16m);});});});});});},_ZG,_15b,_15c,_15d,_15e,_15f);});};_ZX=function(_176,_177,_178,_179,_17a){return new F(function(){return _11t(_176,function(_17b,_17c,_17d){return new F(function(){return _159(_17b,_17c,_177,_178,function(_17e,_17f,_17g){return new F(function(){return A(_177,[_17e,_17f,new T(function(){return B(_x0(_17d,_17g));})]);});},function(_17h){return new F(function(){return A(_178,[new T(function(){return B(_x0(_17d,_17h));})]);});});});},_178,function(_17i,_17j,_17k){return new F(function(){return _159(_17i,_17j,_177,_178,function(_17l,_17m,_17n){return new F(function(){return A(_179,[_17l,_17m,new T(function(){return B(_x0(_17k,_17n));})]);});},function(_17o){return new F(function(){return A(_17a,[new T(function(){return B(_x0(_17k,_17o));})]);});});});},_17a);});};_ZY=_102[2];return null;}})(_ZX,_ZY);if(_ZZ!=null){return _ZZ;}}},_17p=0,_17q=[3,_],_17r=function(_17s,_17t){return [5,_17q,_17s,_17t];},_17u=new T(function(){return B(unCStr("=>"));}),_17v=function(_17w){return E(E(_17w)[1]);},_17x=function(_17y,_17z,_17A,_17B){while(1){var _17C=E(_17B);if(!_17C[0]){return [0,_17y,_17z,_17A];}else{var _17D=_17C[2];switch(E(E(_17C[1])[1])){case 9:var _17E=(_17A+8|0)-B(_zt(_17A-1|0,8))|0;_17B=_17D;_17A=_17E;continue;case 10:var _17F=_17z+1|0;_17A=1;_17B=_17D;_17z=_17F;continue;default:var _17E=_17A+1|0;_17B=_17D;_17A=_17E;continue;}}}},_17G=function(_17H){return E(E(_17H)[1]);},_17I=function(_17J){return E(E(_17J)[2]);},_17K=function(_17L){return [0,E(E(_17L)[2]),_f];},_17M=function(_17N,_17O,_17P,_17Q,_17R,_17S,_17T){var _17U=E(_17O);if(!_17U[0]){return new F(function(){return A(_17S,[_f,_17P,new T(function(){return B(_17K(_17P));})]);});}else{var _17V=E(_17P),_17W=E(_17V[2]),_17X=new T(function(){return B(_17v(_17N));}),_17Y=[0,E(_17W),[1,[2,E([1,_zp,new T(function(){return B(_Bf(_17U,_zq));})])],_zs]],_17Z=[2,E([1,_zp,new T(function(){return B(_Bf(_17U,_zq));})])],_180=new T(function(){var _181=B(_17x(_17W[1],_17W[2],_17W[3],_17U));return [0,_181[1],_181[2],_181[3]];}),_182=function(_183,_184){var _185=E(_183);if(!_185[0]){return new F(function(){return A(_17Q,[_17U,new T(function(){return [0,_184,E(E(_180)),E(_17V[3])];}),new T(function(){return [0,E(E(_180)),_f];})]);});}else{return new F(function(){return A(new T(function(){return B(_17G(_17X));}),[new T(function(){return B(A(new T(function(){return B(_17I(_17N));}),[_184]));}),function(_186){var _187=E(_186);if(!_187[0]){return E(new T(function(){return B(A(_17R,[_17Y]));}));}else{var _188=E(_187[1]),_189=E(_188[1]);return E(_185[1])[1]!=_189[1]?B(A(_17R,[[0,E(_17W),[1,_17Z,[1,[0,E([1,_zp,new T(function(){return B(_Bf([1,_189,_f],_zq));})])],_f]]]])):B(_182(_185[2],_188[2]));}}]);});}};return new F(function(){return A(_17G,[_17X,new T(function(){return B(A(_17I,[_17N,_17V[1]]));}),function(_18a){var _18b=E(_18a);if(!_18b[0]){return E(new T(function(){return B(A(_17T,[_17Y]));}));}else{var _18c=E(_18b[1]),_18d=E(_18c[1]);return E(_17U[1])[1]!=_18d[1]?B(A(_17T,[[0,E(_17W),[1,_17Z,[1,[0,E([1,_zp,new T(function(){return B(_Bf([1,_18d,_f],_zq));})])],_f]]]])):B(_182(_17U[2],_18c[2]));}}]);});}},_18e=function(_18f,_18g,_18h,_18i,_18j){return new F(function(){return _17M(_DV,_17u,_18f,function(_18k,_18l,_18m){return new F(function(){return A(_18g,[_17r,_18l,new T(function(){var _18n=E(E(_18l)[2]),_18o=E(_18m),_18p=E(_18o[1]),_18q=B(_wb(_18p[1],_18p[2],_18p[3],_18o[2],_18n[1],_18n[2],_18n[3],_f));return [0,E(_18q[1]),_18q[2]];})]);});},_18h,function(_18r,_18s,_18t){return new F(function(){return A(_18i,[_17r,_18s,new T(function(){var _18u=E(E(_18s)[2]),_18v=E(_18t),_18w=E(_18v[1]),_18x=B(_wb(_18w[1],_18w[2],_18w[3],_18v[2],_18u[1],_18u[2],_18u[3],_f));return [0,E(_18x[1]),_18x[2]];})]);});},_18j);});},_18y=[0,_18e,_17p],_18z=[1,_18y,_f],_18A=[1,_18z,_f],_18B=1,_18C=[2,_],_18D=function(_17s,_17t){return [5,_18C,_17s,_17t];},_18E=new T(function(){return B(unCStr("\\/"));}),_18F=function(_18G,_18H,_18I,_18J,_18K){return new F(function(){return _17M(_DV,_18E,_18G,function(_18L,_18M,_18N){return new F(function(){return A(_18H,[_18D,_18M,new T(function(){var _18O=E(E(_18M)[2]),_18P=E(_18N),_18Q=E(_18P[1]),_18R=B(_wb(_18Q[1],_18Q[2],_18Q[3],_18P[2],_18O[1],_18O[2],_18O[3],_f));return [0,E(_18R[1]),_18R[2]];})]);});},_18I,function(_18S,_18T,_18U){return new F(function(){return A(_18J,[_18D,_18T,new T(function(){var _18V=E(E(_18T)[2]),_18W=E(_18U),_18X=E(_18W[1]),_18Y=B(_wb(_18X[1],_18X[2],_18X[3],_18W[2],_18V[1],_18V[2],_18V[3],_f));return [0,E(_18Y[1]),_18Y[2]];})]);});},_18K);});},_18Z=[0,_18F,_18B],_190=[1,_],_191=function(_17s,_17t){return [5,_190,_17s,_17t];},_192=new T(function(){return B(unCStr("/\\"));}),_193=function(_194,_195,_196,_197,_198){return new F(function(){return _17M(_DV,_192,_194,function(_199,_19a,_19b){return new F(function(){return A(_195,[_191,_19a,new T(function(){var _19c=E(E(_19a)[2]),_19d=E(_19b),_19e=E(_19d[1]),_19f=B(_wb(_19e[1],_19e[2],_19e[3],_19d[2],_19c[1],_19c[2],_19c[3],_f));return [0,E(_19f[1]),_19f[2]];})]);});},_196,function(_19g,_19h,_19i){return new F(function(){return A(_197,[_191,_19h,new T(function(){var _19j=E(E(_19h)[2]),_19k=E(_19i),_19l=E(_19k[1]),_19m=B(_wb(_19l[1],_19l[2],_19l[3],_19k[2],_19j[1],_19j[2],_19j[3],_f));return [0,E(_19m[1]),_19m[2]];})]);});},_198);});},_19n=[0,_193,_18B],_19o=[1,_19n,_f],_19p=[1,_18Z,_19o],_19q=[1,_19p,_18A],_19r=[0,_],_19s=function(_17t){return [4,_19r,_17t];},_19t=[0,45],_19u=[1,_19t,_f],_19v=function(_19w,_19x,_19y,_19z,_19A){return new F(function(){return _17M(_DV,_19u,_19w,function(_19B,_19C,_19D){return new F(function(){return A(_19x,[_19s,_19C,new T(function(){var _19E=E(E(_19C)[2]),_19F=E(_19D),_19G=E(_19F[1]),_19H=B(_wb(_19G[1],_19G[2],_19G[3],_19F[2],_19E[1],_19E[2],_19E[3],_f));return [0,E(_19H[1]),_19H[2]];})]);});},_19y,function(_19I,_19J,_19K){return new F(function(){return A(_19z,[_19s,_19J,new T(function(){var _19L=E(E(_19J)[2]),_19M=E(_19K),_19N=E(_19M[1]),_19O=B(_wb(_19N[1],_19N[2],_19N[3],_19M[2],_19L[1],_19L[2],_19L[3],_f));return [0,E(_19O[1]),_19O[2]];})]);});},_19A);});},_19P=[1,_19v],_19Q=[1,_19P,_f],_19R=[1,_19Q,_19q],_19S=new T(function(){return B(unCStr("number"));}),_19T=[1,_19S,_f],_19U=new T(function(){return B(err(_E0));}),_19V=new T(function(){return B(err(_DY));}),_19W=new T(function(){return B(_NB(_NX,_No,_O3));}),_19X=function(_19Y){return function(_19Z,_1a0,_1a1,_1a2,_1a3){return new F(function(){return A(_1a2,[new T(function(){var _1a4=B(_O8(B(_E3(_19W,_19Y))));return _1a4[0]==0?E(_19V):E(_1a4[2])[0]==0?E(_1a4[1]):E(_19U);}),_19Z,new T(function(){return [0,E(E(_19Z)[2]),_f];})]);});};},_1a5=function(_1a6,_1a7,_1a8,_1a9,_1aa){return new F(function(){return _x8(_DJ,_1a6,function(_1ab,_1ac,_1ad){return new F(function(){return A(_19X,[_1ab,_1ac,_1a7,_1a8,function(_1ae,_1af,_1ag){return new F(function(){return A(_1a7,[_1ae,_1af,new T(function(){return B(_x0(_1ad,_1ag));})]);});},function(_1ah){return new F(function(){return A(_1a8,[new T(function(){return B(_x0(_1ad,_1ah));})]);});}]);});},_1a8,function(_1ai,_1aj,_1ak){return new F(function(){return A(_19X,[_1ai,_1aj,_1a7,_1a8,function(_1al,_1am,_1an){return new F(function(){return A(_1a9,[_1al,_1am,new T(function(){return B(_x0(_1ak,_1an));})]);});},function(_1ao){return new F(function(){return A(_1aa,[new T(function(){return B(_x0(_1ak,_1ao));})]);});}]);});},_1aa);});},_1ap=function(_1aq,_1ar,_1as,_1at,_1au){return new F(function(){return _1a5(_1aq,function(_1av,_1aw,_1ax){return new F(function(){return A(_1ar,[[1,[0,_,_1av]],_1aw,new T(function(){var _1ay=E(E(_1aw)[2]),_1az=E(_1ax),_1aA=E(_1az[1]),_1aB=B(_wb(_1aA[1],_1aA[2],_1aA[3],_1az[2],_1ay[1],_1ay[2],_1ay[3],_f));return [0,E(_1aB[1]),_1aB[2]];})]);});},_1as,function(_1aC,_1aD,_1aE){return new F(function(){return A(_1at,[[1,[0,_,_1aC]],_1aD,new T(function(){var _1aF=E(E(_1aD)[2]),_1aG=_1aF[1],_1aH=_1aF[2],_1aI=_1aF[3],_1aJ=E(_1aE),_1aK=E(_1aJ[1]),_1aL=_1aK[2],_1aM=_1aK[3],_1aN=E(_1aJ[2]);if(!_1aN[0]){switch(B(_w3(_1aK[1],_1aG))){case 0:var _1aO=[0,E(_1aF),_f];break;case 1:if(_1aL>=_1aH){if(_1aL!=_1aH){var _1aP=[0,E(_1aK),_f];}else{if(_1aM>=_1aI){var _1aQ=_1aM!=_1aI?[0,E(_1aK),_f]:[0,E(_1aK),_wa];}else{var _1aQ=[0,E(_1aF),_f];}var _1aR=_1aQ,_1aP=_1aR;}var _1aS=_1aP,_1aT=_1aS;}else{var _1aT=[0,E(_1aF),_f];}var _1aU=_1aT,_1aO=_1aU;break;default:var _1aO=[0,E(_1aK),_f];}var _1aV=_1aO;}else{var _1aW=B(_Cq(_1aK,_1aN,_19T)),_1aX=E(_1aW[1]),_1aY=B(_wb(_1aX[1],_1aX[2],_1aX[3],_1aW[2],_1aG,_1aH,_1aI,_f)),_1aV=[0,E(_1aY[1]),_1aY[2]];}var _1aZ=_1aV,_1b0=_1aZ,_1b1=_1b0,_1b2=_1b1;return _1b2;})]);});},function(_1b3){return new F(function(){return A(_1au,[new T(function(){var _1b4=E(_1b3),_1b5=B(_Cq(_1b4[1],_1b4[2],_19T));return [0,E(_1b5[1]),_1b5[2]];})]);});});});},_1b6=new T(function(){return B(unCStr("P_"));}),_1b7=function(_1b8,_1b9,_1ba,_1bb,_1bc){return new F(function(){return _17M(_DV,_1b6,_1b8,function(_1bd,_1be,_1bf){return new F(function(){return _1ap(_1be,_1b9,_1ba,function(_1bg,_1bh,_1bi){return new F(function(){return A(_1b9,[_1bg,_1bh,new T(function(){return B(_x0(_1bf,_1bi));})]);});},function(_1bj){return new F(function(){return A(_1ba,[new T(function(){return B(_x0(_1bf,_1bj));})]);});});});},_1ba,function(_1bk,_1bl,_1bm){return new F(function(){return _1ap(_1bl,_1b9,_1ba,function(_1bn,_1bo,_1bp){return new F(function(){return A(_1bb,[_1bn,_1bo,new T(function(){return B(_x0(_1bm,_1bp));})]);});},function(_1bq){return new F(function(){return A(_1bc,[new T(function(){return B(_x0(_1bm,_1bq));})]);});});});},_1bc);});},_1br=[0,41],_1bs=new T(function(){return B(_D2(_DV,_1br));}),_1bt=function(_1bu,_1bv,_1bw,_1bx,_1by,_1bz){return new F(function(){return A(_1bs,[_1bv,function(_1bA,_1bB,_1bC){return new F(function(){return A(_1bw,[_1bu,_1bB,new T(function(){var _1bD=E(E(_1bB)[2]),_1bE=E(_1bC),_1bF=E(_1bE[1]),_1bG=B(_wb(_1bF[1],_1bF[2],_1bF[3],_1bE[2],_1bD[1],_1bD[2],_1bD[3],_f));return [0,E(_1bG[1]),_1bG[2]];})]);});},_1bx,function(_1bH,_1bI,_1bJ){return new F(function(){return A(_1by,[_1bu,_1bI,new T(function(){var _1bK=E(E(_1bI)[2]),_1bL=E(_1bJ),_1bM=E(_1bL[1]),_1bN=B(_wb(_1bM[1],_1bM[2],_1bM[3],_1bL[2],_1bK[1],_1bK[2],_1bK[3],_f));return [0,E(_1bN[1]),_1bN[2]];})]);});},_1bz]);});},_1bO=function(_1bP,_1bQ,_1bR,_1bS,_1bT){return new F(function(){return A(_1bU,[_1bP,function(_1bV,_1bW,_1bX){return new F(function(){return _1bt(_1bV,_1bW,_1bQ,_1bR,function(_1bY,_1bZ,_1c0){return new F(function(){return A(_1bQ,[_1bY,_1bZ,new T(function(){return B(_x0(_1bX,_1c0));})]);});},function(_1c1){return new F(function(){return A(_1bR,[new T(function(){return B(_x0(_1bX,_1c1));})]);});});});},_1bR,function(_1c2,_1c3,_1c4){return new F(function(){return _1bt(_1c2,_1c3,_1bQ,_1bR,function(_1c5,_1c6,_1c7){return new F(function(){return A(_1bS,[_1c5,_1c6,new T(function(){return B(_x0(_1c4,_1c7));})]);});},function(_1c8){return new F(function(){return A(_1bT,[new T(function(){return B(_x0(_1c4,_1c8));})]);});});});},_1bT]);});},_1c9=[0,40],_1ca=new T(function(){return B(_D2(_DV,_1c9));}),_1cb=function(_1cc,_1cd,_1ce,_1cf,_1cg){var _1ch=function(_1ci){return new F(function(){return _1b7(_1cc,_1cd,_1ce,function(_1cj,_1ck,_1cl){return new F(function(){return A(_1cf,[_1cj,_1ck,new T(function(){return B(_x0(_1ci,_1cl));})]);});},function(_1cm){return new F(function(){return A(_1cg,[new T(function(){return B(_x0(_1ci,_1cm));})]);});});});};return new F(function(){return A(_1ca,[_1cc,function(_1cn,_1co,_1cp){return new F(function(){return _1bO(_1co,_1cd,_1ce,function(_1cq,_1cr,_1cs){return new F(function(){return A(_1cd,[_1cq,_1cr,new T(function(){return B(_x0(_1cp,_1cs));})]);});},function(_1ct){return new F(function(){return A(_1ce,[new T(function(){return B(_x0(_1cp,_1ct));})]);});});});},_1ce,function(_1cu,_1cv,_1cw){return new F(function(){return _1bO(_1cv,_1cd,_1ce,function(_1cx,_1cy,_1cz){return new F(function(){return A(_1cf,[_1cx,_1cy,new T(function(){return B(_x0(_1cw,_1cz));})]);});},function(_1cA){return new F(function(){return _1ch(new T(function(){return B(_x0(_1cw,_1cA));}));});});});},_1ch]);});},_1bU=new T(function(){return B(_ZW(_1cb,_19R));}),_1cB=function(_1cC,_1cD,_1cE,_1cF,_1cG){return new F(function(){return A(_1bU,[_1cC,function(_1cH,_1cI,_1cJ){return new F(function(){return _Y6(_1cH,_1cI,_1cD,_1cE,function(_1cK,_1cL,_1cM){return new F(function(){return A(_1cD,[_1cK,_1cL,new T(function(){return B(_x0(_1cJ,_1cM));})]);});},function(_1cN){return new F(function(){return A(_1cE,[new T(function(){return B(_x0(_1cJ,_1cN));})]);});});});},_1cE,function(_1cO,_1cP,_1cQ){return new F(function(){return _Y6(_1cO,_1cP,_1cD,_1cE,function(_1cR,_1cS,_1cT){return new F(function(){return A(_1cF,[_1cR,_1cS,new T(function(){return B(_x0(_1cQ,_1cT));})]);});},function(_1cU){return new F(function(){return A(_1cG,[new T(function(){return B(_x0(_1cQ,_1cU));})]);});});});},_1cG]);});},_1cV=function(_1cW,_1cX,_1cY,_1cZ,_1d0){return new F(function(){return _xL(_C7,_1cW,function(_1d1,_1d2,_1d3){return new F(function(){return _1cB(_1d2,_1cX,_1cY,function(_1d4,_1d5,_1d6){return new F(function(){return A(_1cX,[_1d4,_1d5,new T(function(){return B(_x0(_1d3,_1d6));})]);});},function(_1d7){return new F(function(){return A(_1cY,[new T(function(){return B(_x0(_1d3,_1d7));})]);});});});},_1cY,function(_1d8,_1d9,_1da){return new F(function(){return _1cB(_1d9,_1cX,_1cY,function(_1db,_1dc,_1dd){return new F(function(){return A(_1cZ,[_1db,_1dc,new T(function(){return B(_x0(_1da,_1dd));})]);});},function(_1de){return new F(function(){return A(_1d0,[new T(function(){return B(_x0(_1da,_1de));})]);});});});});});},_1df=function(_1dg,_1dh,_1di,_1dj,_1dk,_1dl,_1dm,_1dn){var _1do=E(_1dg);if(!_1do[0]){return new F(function(){return A(_1dn,[[0,E([0,_1dh,_1di,_1dj]),_zs]]);});}else{var _1dp=_1do[1];if(!B(_82(_BN,_1dp,_QA))){return new F(function(){return A(_1dn,[[0,E([0,_1dh,_1di,_1dj]),[1,[0,E([1,_zp,new T(function(){return B(_Bf([1,_1dp,_f],_zq));})])],_f]]]);});}else{var _1dq=function(_1dr,_1ds,_1dt,_1du){var _1dv=[0,E([0,_1dr,_1ds,_1dt]),_f],_1dw=[0,E([0,_1dr,_1ds,_1dt]),_wa];return new F(function(){return _xL(_R7,[0,_1do[2],E(_1du),E(_1dk)],function(_1dx,_1dy,_1dz){return new F(function(){return _1cV(_1dy,_1dl,_1dm,function(_1dA,_1dB,_1dC){return new F(function(){return A(_1dl,[_1dA,_1dB,new T(function(){return B(_x0(_1dz,_1dC));})]);});},function(_1dD){return new F(function(){return A(_1dm,[new T(function(){return B(_x0(_1dz,_1dD));})]);});});});},_1dm,function(_1dE,_1dF,_1dG){return new F(function(){return _1cV(_1dF,_1dl,_1dm,function(_1dH,_1dI,_1dJ){return new F(function(){return A(_1dl,[_1dH,_1dI,new T(function(){var _1dK=E(_1dG),_1dL=E(_1dK[1]),_1dM=E(_1dJ),_1dN=E(_1dM[1]),_1dO=B(_wb(_1dL[1],_1dL[2],_1dL[3],_1dK[2],_1dN[1],_1dN[2],_1dN[3],_1dM[2])),_1dP=E(_1dO[1]),_1dQ=_1dP[2],_1dR=_1dP[3],_1dS=E(_1dO[2]);if(!_1dS[0]){switch(B(_w3(_1dr,_1dP[1]))){case 0:var _1dT=[0,E(_1dP),_f];break;case 1:if(_1ds>=_1dQ){if(_1ds!=_1dQ){var _1dU=E(_1dv);}else{if(_1dt>=_1dR){var _1dV=_1dt!=_1dR?E(_1dv):E(_1dw);}else{var _1dV=[0,E(_1dP),_f];}var _1dW=_1dV,_1dU=_1dW;}var _1dX=_1dU,_1dY=_1dX;}else{var _1dY=[0,E(_1dP),_f];}var _1dZ=_1dY,_1dT=_1dZ;break;default:var _1dT=E(_1dv);}var _1e0=_1dT;}else{var _1e0=[0,E(_1dP),_1dS];}var _1e1=_1e0,_1e2=_1e1,_1e3=_1e2,_1e4=_1e3,_1e5=_1e4,_1e6=_1e5;return _1e6;})]);});},function(_1e7){return new F(function(){return A(_1dm,[new T(function(){var _1e8=E(_1dG),_1e9=E(_1e8[1]),_1ea=E(_1e7),_1eb=E(_1ea[1]),_1ec=B(_wb(_1e9[1],_1e9[2],_1e9[3],_1e8[2],_1eb[1],_1eb[2],_1eb[3],_1ea[2])),_1ed=E(_1ec[1]),_1ee=_1ed[2],_1ef=_1ed[3],_1eg=E(_1ec[2]);if(!_1eg[0]){switch(B(_w3(_1dr,_1ed[1]))){case 0:var _1eh=[0,E(_1ed),_f];break;case 1:if(_1ds>=_1ee){if(_1ds!=_1ee){var _1ei=E(_1dv);}else{if(_1dt>=_1ef){var _1ej=_1dt!=_1ef?E(_1dv):E(_1dw);}else{var _1ej=[0,E(_1ed),_f];}var _1ek=_1ej,_1ei=_1ek;}var _1el=_1ei,_1em=_1el;}else{var _1em=[0,E(_1ed),_f];}var _1en=_1em,_1eh=_1en;break;default:var _1eh=E(_1dv);}var _1eo=_1eh;}else{var _1eo=[0,E(_1ed),_1eg];}var _1ep=_1eo,_1eq=_1ep,_1er=_1eq,_1es=_1er,_1et=_1es,_1eu=_1et;return _1eu;})]);});});});});});};switch(E(E(_1dp)[1])){case 9:var _1ev=(_1dj+8|0)-B(_zt(_1dj-1|0,8))|0;return new F(function(){return _1dq(_1dh,_1di,_1ev,[0,_1dh,_1di,_1ev]);});break;case 10:var _1ew=_1di+1|0;return new F(function(){return _1dq(_1dh,_1ew,1,[0,_1dh,_1ew,1]);});break;default:var _1ex=_1dj+1|0;return new F(function(){return _1dq(_1dh,_1di,_1ex,[0,_1dh,_1di,_1ex]);});}}}},_1ey=function(_1ez,_1eA,_1eB,_1eC,_1eD,_1eE){var _1eF=function(_1eG,_1eH,_1eI,_1eJ,_1eK,_1eL){var _1eM=function(_1eN){var _1eO=[0,[1,[0,_1ez,_1eG,new T(function(){return B(_7T(_Of,_1eN));})]],_f];return function(_1eP,_1eQ,_1eR,_1eS,_1eT){return new F(function(){return A(_Dt,[_1eP,function(_1eU,_1eV,_1eW){return new F(function(){return A(_1eQ,[_1eO,_1eV,new T(function(){var _1eX=E(E(_1eV)[2]),_1eY=E(_1eW),_1eZ=E(_1eY[1]),_1f0=B(_wb(_1eZ[1],_1eZ[2],_1eZ[3],_1eY[2],_1eX[1],_1eX[2],_1eX[3],_f));return [0,E(_1f0[1]),_1f0[2]];})]);});},_1eT,function(_1f1,_1f2,_1f3){return new F(function(){return A(_1eS,[_1eO,_1f2,new T(function(){var _1f4=E(E(_1f2)[2]),_1f5=E(_1f3),_1f6=E(_1f5[1]),_1f7=B(_wb(_1f6[1],_1f6[2],_1f6[3],_1f5[2],_1f4[1],_1f4[2],_1f4[3],_f));return [0,E(_1f7[1]),_1f7[2]];})]);});},_1eT]);});};},_1f8=function(_1f9,_1fa,_1fb,_1fc,_1fd){var _1fe=function(_1ff,_1fg,_1fh){return new F(function(){return A(_1eM,[_1ff,_1fg,_1fa,_1fb,function(_1fi,_1fj,_1fk){return new F(function(){return A(_1fc,[_1fi,_1fj,new T(function(){return B(_x0(_1fh,_1fk));})]);});},function(_1fl){return new F(function(){return A(_1fd,[new T(function(){return B(_x0(_1fh,_1fl));})]);});}]);});},_1fm=function(_1fn){return new F(function(){return _1fe(_f,_1f9,new T(function(){var _1fo=E(E(_1f9)[2]),_1fp=E(_1fn),_1fq=E(_1fp[1]),_1fr=B(_wb(_1fq[1],_1fq[2],_1fq[3],_1fp[2],_1fo[1],_1fo[2],_1fo[3],_f));return [0,E(_1fr[1]),_1fr[2]];}));});};return new F(function(){return _yb(_DP,_DX,_1f9,function(_1fs,_1ft,_1fu){return new F(function(){return A(_1eM,[_1fs,_1ft,_1fa,_1fb,function(_1fv,_1fw,_1fx){return new F(function(){return A(_1fa,[_1fv,_1fw,new T(function(){return B(_x0(_1fu,_1fx));})]);});},function(_1fy){return new F(function(){return A(_1fb,[new T(function(){return B(_x0(_1fu,_1fy));})]);});}]);});},_1fm,_1fe,_1fm);});};return new F(function(){return _xL(_C7,_1eH,function(_1fz,_1fA,_1fB){return new F(function(){return _1f8(_1fA,_1eI,_1eJ,function(_1fC,_1fD,_1fE){return new F(function(){return A(_1eI,[_1fC,_1fD,new T(function(){return B(_x0(_1fB,_1fE));})]);});},function(_1fF){return new F(function(){return A(_1eJ,[new T(function(){return B(_x0(_1fB,_1fF));})]);});});});},_1eJ,function(_1fG,_1fH,_1fI){return new F(function(){return _1f8(_1fH,_1eI,_1eJ,function(_1fJ,_1fK,_1fL){return new F(function(){return A(_1eK,[_1fJ,_1fK,new T(function(){return B(_x0(_1fI,_1fL));})]);});},function(_1fM){return new F(function(){return A(_1eL,[new T(function(){return B(_x0(_1fI,_1fM));})]);});});});});});},_1fN=function(_1fO,_1fP,_1fQ,_1fR,_1fS){return new F(function(){return _x8(_PE,_1fO,function(_1fT,_1fU,_1fV){return new F(function(){return _1eF(_1fT,_1fU,_1fP,_1fQ,function(_1fW,_1fX,_1fY){return new F(function(){return A(_1fP,[_1fW,_1fX,new T(function(){return B(_x0(_1fV,_1fY));})]);});},function(_1fZ){return new F(function(){return A(_1fQ,[new T(function(){return B(_x0(_1fV,_1fZ));})]);});});});},_1fS,function(_1g0,_1g1,_1g2){return new F(function(){return _1eF(_1g0,_1g1,_1fP,_1fQ,function(_1g3,_1g4,_1g5){return new F(function(){return A(_1fR,[_1g3,_1g4,new T(function(){return B(_x0(_1g2,_1g5));})]);});},function(_1g6){return new F(function(){return A(_1fS,[new T(function(){return B(_x0(_1g2,_1g6));})]);});});});},_1fS);});};return new F(function(){return _xL(_C7,_1eA,function(_1g7,_1g8,_1g9){return new F(function(){return _1fN(_1g8,_1eB,_1eC,function(_1ga,_1gb,_1gc){return new F(function(){return A(_1eB,[_1ga,_1gb,new T(function(){return B(_x0(_1g9,_1gc));})]);});},function(_1gd){return new F(function(){return A(_1eC,[new T(function(){return B(_x0(_1g9,_1gd));})]);});});});},_1eC,function(_1ge,_1gf,_1gg){return new F(function(){return _1fN(_1gf,_1eB,_1eC,function(_1gh,_1gi,_1gj){return new F(function(){return A(_1eD,[_1gh,_1gi,new T(function(){return B(_x0(_1gg,_1gj));})]);});},function(_1gk){return new F(function(){return A(_1eE,[new T(function(){return B(_x0(_1gg,_1gk));})]);});});});});});},_1gl=function(_1gm,_1gn,_1go,_1gp,_1gq){return new F(function(){return A(_1bU,[_1gm,function(_1gr,_1gs,_1gt){return new F(function(){return _1ey(_1gr,_1gs,_1gn,_1go,function(_1gu,_1gv,_1gw){return new F(function(){return A(_1gn,[_1gu,_1gv,new T(function(){return B(_x0(_1gt,_1gw));})]);});},function(_1gx){return new F(function(){return A(_1go,[new T(function(){return B(_x0(_1gt,_1gx));})]);});});});},_1go,function(_1gy,_1gz,_1gA){return new F(function(){return _1ey(_1gy,_1gz,_1gn,_1go,function(_1gB,_1gC,_1gD){return new F(function(){return A(_1gp,[_1gB,_1gC,new T(function(){return B(_x0(_1gA,_1gD));})]);});},function(_1gE){return new F(function(){return A(_1gq,[new T(function(){return B(_x0(_1gA,_1gE));})]);});});});},_1gq]);});},_1gF=function(_1gG,_1gH,_1gI,_1gJ,_1gK){return new F(function(){return _1gl(_1gG,_1gH,_1gI,_1gJ,function(_1gL){var _1gM=E(_1gG),_1gN=E(_1gM[2]);return new F(function(){return _1df(_1gM[1],_1gN[1],_1gN[2],_1gN[3],_1gM[3],_1gH,_1gI,function(_1gO){return new F(function(){return A(_1gK,[new T(function(){return B(_x0(_1gL,_1gO));})]);});});});});});},_1gP=function(_1gQ,_1gR,_1gS,_1gT){return new F(function(){return _wy(_1gF,_1gQ,function(_1gU,_1gV,_1gW){return new F(function(){return _Q6(_1gU,_1gV,_1gR,function(_1gX,_1gY,_1gZ){return new F(function(){return A(_1gR,[_1gX,_1gY,new T(function(){return B(_x0(_1gW,_1gZ));})]);});});});},_1gS,function(_1h0,_1h1,_1h2){return new F(function(){return _Q6(_1h0,_1h1,_1gR,function(_1h3,_1h4,_1h5){return new F(function(){return A(_1gT,[_1h3,_1h4,new T(function(){return B(_x0(_1h2,_1h5));})]);});});});});});},_XE=function(_1h6,_1h7,_1h8,_1h9,_1ha){return new F(function(){return _1gP(_1h6,_1h7,_1h8,_1h9);});},_1hb=new T(function(){return B(unCStr("ADD"));}),_1hc=new T(function(){return B(unCStr("ADJ"));}),_1hd=[0,1],_1he=[1,_1hd],_1hf=[1,_1he],_1hg=new T(function(){return B(unCStr("MTP"));}),_1hh=new T(function(){return B(unCStr("MP"));}),_1hi=new T(function(){return B(unCStr("ID"));}),_1hj=new T(function(){return B(unCStr("CD"));}),_1hk=[0,2],_1hl=[1,_1hk],_1hm=[1,_1hl],_1hn=[0,_1hk],_1ho=[1,_1hn],_1hp=[0,_1hd],_1hq=[1,_1hp],_1hr=function(_1hs){if(!B(_bv(_1hs,_1hb))){if(!B(_bv(_1hs,_1hc))){if(!B(_bv(_1hs,_1hj))){if(!B(_bv(_1hs,_1hi))){if(!B(_bv(_1hs,_1hh))){if(!B(_bv(_1hs,_1hg))){var _1ht=E(_1hs);return _1ht[0]==0?[0]:E(E(_1ht[1])[1])==83?E(_1ht[2])[0]==0?E(_1hq):[0]:[0];}else{return E(_1ho);}}else{return E(_1ho);}}else{return E(_1hm);}}else{return E(_1hf);}}else{return E(_1ho);}}else{return E(_1ho);}},_1hu=function(_1hv){return E(E(_1hv)[2]);},_1hw=function(_1hx,_1hy,_1hz){while(1){var _1hA=E(_1hy);if(!_1hA[0]){return E(_1hz)[0]==0?1:0;}else{var _1hB=E(_1hz);if(!_1hB[0]){return 2;}else{var _1hC=B(A(_1hu,[_1hx,_1hA[1],_1hB[1]]));if(_1hC==1){_1hy=_1hA[2];_1hz=_1hB[2];continue;}else{return E(_1hC);}}}}},_1hD=function(_1hE){return E(E(_1hE)[3]);},_1hF=function(_1hG,_1hH,_1hI,_1hJ,_1hK){switch(B(_1hw(_1hG,_1hH,_1hJ))){case 0:return true;case 1:return new F(function(){return A(_1hD,[_1hG,_1hI,_1hK]);});break;default:return false;}},_1hL=function(_1hM,_1hN,_1hO,_1hP){var _1hQ=E(_1hO),_1hR=E(_1hP);return new F(function(){return _1hF(_1hN,_1hQ[1],_1hQ[2],_1hR[1],_1hR[2]);});},_1hS=function(_1hT){return E(E(_1hT)[6]);},_1hU=function(_1hV,_1hW,_1hX,_1hY,_1hZ){switch(B(_1hw(_1hV,_1hW,_1hY))){case 0:return true;case 1:return new F(function(){return A(_1hS,[_1hV,_1hX,_1hZ]);});break;default:return false;}},_1i0=function(_1i1,_1i2,_1i3,_1i4){var _1i5=E(_1i3),_1i6=E(_1i4);return new F(function(){return _1hU(_1i2,_1i5[1],_1i5[2],_1i6[1],_1i6[2]);});},_1i7=function(_1i8){return E(E(_1i8)[5]);},_1i9=function(_1ia,_1ib,_1ic,_1id,_1ie){switch(B(_1hw(_1ia,_1ib,_1id))){case 0:return false;case 1:return new F(function(){return A(_1i7,[_1ia,_1ic,_1ie]);});break;default:return true;}},_1if=function(_1ig,_1ih,_1ii,_1ij){var _1ik=E(_1ii),_1il=E(_1ij);return new F(function(){return _1i9(_1ih,_1ik[1],_1ik[2],_1il[1],_1il[2]);});},_1im=function(_1in){return E(E(_1in)[4]);},_1io=function(_1ip,_1iq,_1ir,_1is,_1it){switch(B(_1hw(_1ip,_1iq,_1is))){case 0:return false;case 1:return new F(function(){return A(_1im,[_1ip,_1ir,_1it]);});break;default:return true;}},_1iu=function(_1iv,_1iw,_1ix,_1iy){var _1iz=E(_1ix),_1iA=E(_1iy);return new F(function(){return _1io(_1iw,_1iz[1],_1iz[2],_1iA[1],_1iA[2]);});},_1iB=function(_1iC,_1iD,_1iE,_1iF,_1iG){switch(B(_1hw(_1iC,_1iD,_1iF))){case 0:return 0;case 1:return new F(function(){return A(_1hu,[_1iC,_1iE,_1iG]);});break;default:return 2;}},_1iH=function(_1iI,_1iJ,_1iK,_1iL){var _1iM=E(_1iK),_1iN=E(_1iL);return new F(function(){return _1iB(_1iJ,_1iM[1],_1iM[2],_1iN[1],_1iN[2]);});},_1iO=function(_1iP,_1iQ,_1iR,_1iS){var _1iT=E(_1iR),_1iU=_1iT[1],_1iV=_1iT[2],_1iW=E(_1iS),_1iX=_1iW[1],_1iY=_1iW[2];switch(B(_1hw(_1iQ,_1iU,_1iX))){case 0:return [0,_1iX,_1iY];case 1:return !B(A(_1hS,[_1iQ,_1iV,_1iY]))?[0,_1iU,_1iV]:[0,_1iX,_1iY];default:return [0,_1iU,_1iV];}},_1iZ=function(_1j0,_1j1,_1j2,_1j3){var _1j4=E(_1j2),_1j5=_1j4[1],_1j6=_1j4[2],_1j7=E(_1j3),_1j8=_1j7[1],_1j9=_1j7[2];switch(B(_1hw(_1j1,_1j5,_1j8))){case 0:return [0,_1j5,_1j6];case 1:return !B(A(_1hS,[_1j1,_1j6,_1j9]))?[0,_1j8,_1j9]:[0,_1j5,_1j6];default:return [0,_1j8,_1j9];}},_1ja=function(_1jb,_1jc){return [0,_1jb,function(_bt,_bu){return new F(function(){return _1iH(_1jb,_1jc,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1hL(_1jb,_1jc,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1iu(_1jb,_1jc,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1if(_1jb,_1jc,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1i0(_1jb,_1jc,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1iO(_1jb,_1jc,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1iZ(_1jb,_1jc,_bt,_bu);});}];},_1jd=function(_1je,_1jf,_1jg,_1jh){return !B(A(_1je,[_1jg,_1jh]))?B(_w3(B(A(_1jf,[_1jg,_j3])),B(A(_1jf,[_1jh,_j3]))))==2?false:true:false;},_1ji=function(_1jj,_1jk,_1jl,_1jm){return new F(function(){return _1jd(E(_1jj)[1],_1jk,_1jl,_1jm);});},_1jn=function(_1jo,_1jp,_1jq,_1jr){return B(_w3(B(A(_1jp,[_1jq,_j3])),B(A(_1jp,[_1jr,_j3]))))==2?false:true;},_1js=function(_1jt,_1ju,_1jv,_1jw){return !B(A(_1jt,[_1jv,_1jw]))?B(_w3(B(A(_1ju,[_1jv,_j3])),B(A(_1ju,[_1jw,_j3]))))==2?true:false:false;},_1jx=function(_1jy,_1jz,_1jA,_1jB){return new F(function(){return _1js(E(_1jy)[1],_1jz,_1jA,_1jB);});},_1jC=function(_1jD,_1jE,_1jF,_1jG){return !B(A(_1jD,[_1jF,_1jG]))?B(_w3(B(A(_1jE,[_1jF,_j3])),B(A(_1jE,[_1jG,_j3]))))==2?true:false:true;},_1jH=function(_1jI,_1jJ,_1jK,_1jL){return new F(function(){return _1jC(E(_1jI)[1],_1jJ,_1jK,_1jL);});},_1jM=function(_1jN,_1jO,_1jP,_1jQ){return !B(A(_1jN,[_1jP,_1jQ]))?B(_w3(B(A(_1jO,[_1jP,_j3])),B(A(_1jO,[_1jQ,_j3]))))==2?2:0:1;},_1jR=function(_1jS,_1jT,_1jU,_1jV){return new F(function(){return _1jM(E(_1jS)[1],_1jT,_1jU,_1jV);});},_1jW=function(_1jX,_1jY,_1jZ,_1k0){return B(_w3(B(A(_1jY,[_1jZ,_j3])),B(A(_1jY,[_1k0,_j3]))))==2?E(_1jZ):E(_1k0);},_1k1=function(_1k2,_1k3,_1k4,_1k5){return B(_w3(B(A(_1k3,[_1k4,_j3])),B(A(_1k3,[_1k5,_j3]))))==2?E(_1k5):E(_1k4);},_1k6=function(_1k7,_1k8){return [0,_1k7,function(_c2,_c3){return new F(function(){return _1jR(_1k7,_1k8,_c2,_c3);});},function(_c2,_c3){return new F(function(){return _1ji(_1k7,_1k8,_c2,_c3);});},function(_c2,_c3){return new F(function(){return _1jH(_1k7,_1k8,_c2,_c3);});},function(_c2,_c3){return new F(function(){return _1jx(_1k7,_1k8,_c2,_c3);});},function(_c2,_c3){return new F(function(){return _1jn(_1k7,_1k8,_c2,_c3);});},function(_c2,_c3){return new F(function(){return _1jW(_1k7,_1k8,_c2,_c3);});},function(_c2,_c3){return new F(function(){return _1k1(_1k7,_1k8,_c2,_c3);});}];},_1k9=function(_1ka,_1kb,_1kc,_1kd,_1ke,_1kf,_1kg){var _1kh=function(_1ki,_1kj){return new F(function(){return _an(_1ka,_1kb,_1kc,_1ke,_1kd,_1kg,_1kf,_1ki);});};return function(_1kk,_1kl){var _1km=E(_1kk);if(!_1km[0]){var _1kn=E(_1kl);return _1kn[0]==0?B(_w3(B(_a9(_1km[1])),B(_a9(_1kn[1]))))==2?false:true:true;}else{var _1ko=E(_1kl);return _1ko[0]==0?false:B(_1hw(new T(function(){return B(_1k6(new T(function(){return B(_j8(_1kh));}),_1kh));}),_1km[1],_1ko[1]))==2?false:true;}};},_1kp=function(_1kq,_1kr,_1ks,_1kt,_1ku,_1kv,_1kw,_1kx,_1ky,_1kz){return !B(A(_1k9,[_1kr,_1ks,_1kt,_1ku,_1kv,_1kw,_1kx,_1ky,_1kz]))?E(_1ky):E(_1kz);},_1kA=function(_1kB,_1kC,_1kD,_1kE,_1kF,_1kG,_1kH,_1kI,_1kJ,_1kK){return !B(A(_1k9,[_1kC,_1kD,_1kE,_1kF,_1kG,_1kH,_1kI,_1kJ,_1kK]))?E(_1kK):E(_1kJ);},_1kL=function(_1kM,_1kN,_1kO,_1kP,_1kQ,_1kR,_1kS){var _1kT=function(_1kU,_1kV){return new F(function(){return _an(_1kM,_1kN,_1kO,_1kQ,_1kP,_1kS,_1kR,_1kU);});};return function(_1kW,_1kX){var _1kY=E(_1kW);if(!_1kY[0]){var _1kZ=_1kY[1],_1l0=E(_1kX);if(!_1l0[0]){var _1l1=_1l0[1];return B(_ci(_1kZ,_1l1,_60))[0]==0?B(_w3(B(_a9(_1kZ)),B(_a9(_1l1))))==2?false:true:false;}else{return true;}}else{var _1l2=E(_1kX);return _1l2[0]==0?false:B(_1hw(new T(function(){return B(_1k6(new T(function(){return B(_j8(_1kT));}),_1kT));}),_1kY[1],_1l2[1]))==0?true:false;}};},_1l3=function(_1l4,_1l5,_1l6,_1l7,_1l8,_1l9,_1la){var _1lb=function(_1lc,_1ld){return new F(function(){return _an(_1l4,_1l5,_1l6,_1l8,_1l7,_1la,_1l9,_1lc);});};return function(_1le,_1lf){var _1lg=E(_1le);if(!_1lg[0]){var _1lh=_1lg[1],_1li=E(_1lf);if(!_1li[0]){var _1lj=_1li[1];return B(_ci(_1lh,_1lj,_60))[0]==0?B(_w3(B(_a9(_1lh)),B(_a9(_1lj))))==2?true:false:false;}else{return false;}}else{var _1lk=E(_1lf);return _1lk[0]==0?true:B(_1hw(new T(function(){return B(_1k6(new T(function(){return B(_j8(_1lb));}),_1lb));}),_1lg[1],_1lk[1]))==2?true:false;}};},_1ll=function(_1lm,_1ln,_1lo,_1lp,_1lq,_1lr,_1ls){var _1lt=function(_1lu,_1lv){return new F(function(){return _an(_1lm,_1ln,_1lo,_1lq,_1lp,_1ls,_1lr,_1lu);});};return function(_1lw,_1lx){var _1ly=E(_1lw);if(!_1ly[0]){var _1lz=_1ly[1],_1lA=E(_1lx);if(!_1lA[0]){var _1lB=_1lA[1];return B(_ci(_1lz,_1lB,_60))[0]==0?B(_w3(B(_a9(_1lz)),B(_a9(_1lB))))==2?true:false:true;}else{return false;}}else{var _1lC=E(_1lx);return _1lC[0]==0?true:B(_1hw(new T(function(){return B(_1k6(new T(function(){return B(_j8(_1lt));}),_1lt));}),_1ly[1],_1lC[1]))==0?false:true;}};},_1lD=function(_1lE,_1lF,_1lG,_1lH,_1lI,_1lJ,_1lK){var _1lL=function(_1lM,_1lN){return new F(function(){return _an(_1lE,_1lF,_1lG,_1lI,_1lH,_1lK,_1lJ,_1lM);});};return function(_1lO,_1lP){var _1lQ=E(_1lO);if(!_1lQ[0]){var _1lR=_1lQ[1],_1lS=E(_1lP);if(!_1lS[0]){var _1lT=_1lS[1];return B(_ci(_1lR,_1lT,_60))[0]==0?B(_w3(B(_a9(_1lR)),B(_a9(_1lT))))==2?2:0:1;}else{return 0;}}else{var _1lU=E(_1lP);return _1lU[0]==0?2:B(_1hw(new T(function(){return B(_1k6(new T(function(){return B(_j8(_1lL));}),_1lL));}),_1lQ[1],_1lU[1]));}};},_1lV=function(_1lW,_1lX,_1lY,_1lZ,_1m0,_1m1,_1m2,_1m3){return [0,_1lW,new T(function(){return B(_1lD(_1lX,_1lY,_1lZ,_1m0,_1m1,_1m2,_1m3));}),new T(function(){return B(_1kL(_1lX,_1lY,_1lZ,_1m0,_1m1,_1m2,_1m3));}),new T(function(){return B(_1ll(_1lX,_1lY,_1lZ,_1m0,_1m1,_1m2,_1m3));}),new T(function(){return B(_1l3(_1lX,_1lY,_1lZ,_1m0,_1m1,_1m2,_1m3));}),new T(function(){return B(_1k9(_1lX,_1lY,_1lZ,_1m0,_1m1,_1m2,_1m3));}),function(_c2,_c3){return new F(function(){return _1kp(_1lW,_1lX,_1lY,_1lZ,_1m0,_1m1,_1m2,_1m3,_c2,_c3);});},function(_c2,_c3){return new F(function(){return _1kA(_1lW,_1lX,_1lY,_1lZ,_1m0,_1m1,_1m2,_1m3,_c2,_c3);});}];},_1m4=new T(function(){return B(_bU(_6x,_6o,_6x,_6x,_6u,_61,_6M));}),_1m5=new T(function(){return B(_1lV(_1m4,_6x,_6o,_6x,_6x,_6u,_6M,_61));}),_1m6=new T(function(){return B(_cg(_1m4));}),_1m7=new T(function(){return B(_1ja(_1m6,_1m5));}),_1m8=function(_1m9,_1ma,_1mb,_1mc){var _1md=E(_1mb),_1me=E(_1mc);return new F(function(){return _1hF(_1ma,_1md[1],_1md[2],_1me[1],_1me[2]);});},_1mf=function(_1mg,_1mh,_1mi,_1mj){var _1mk=E(_1mi),_1ml=E(_1mj);return new F(function(){return _1hU(_1mh,_1mk[1],_1mk[2],_1ml[1],_1ml[2]);});},_1mm=function(_1mn,_1mo,_1mp,_1mq){var _1mr=E(_1mp),_1ms=E(_1mq);return new F(function(){return _1i9(_1mo,_1mr[1],_1mr[2],_1ms[1],_1ms[2]);});},_1mt=function(_1mu,_1mv,_1mw,_1mx){var _1my=E(_1mw),_1mz=E(_1mx);return new F(function(){return _1io(_1mv,_1my[1],_1my[2],_1mz[1],_1mz[2]);});},_1mA=function(_1mB,_1mC,_1mD,_1mE){var _1mF=E(_1mD),_1mG=E(_1mE);return new F(function(){return _1iB(_1mC,_1mF[1],_1mF[2],_1mG[1],_1mG[2]);});},_1mH=function(_1mI,_1mJ,_1mK,_1mL){var _1mM=E(_1mK),_1mN=_1mM[1],_1mO=_1mM[2],_1mP=E(_1mL),_1mQ=_1mP[1],_1mR=_1mP[2];switch(B(_1hw(_1mJ,_1mN,_1mQ))){case 0:return [0,_1mQ,_1mR];case 1:return !B(A(_1hS,[_1mJ,_1mO,_1mR]))?[0,_1mN,_1mO]:[0,_1mQ,_1mR];default:return [0,_1mN,_1mO];}},_1mS=function(_1mT,_1mU,_1mV,_1mW){var _1mX=E(_1mV),_1mY=_1mX[1],_1mZ=_1mX[2],_1n0=E(_1mW),_1n1=_1n0[1],_1n2=_1n0[2];switch(B(_1hw(_1mU,_1mY,_1n1))){case 0:return [0,_1mY,_1mZ];case 1:return !B(A(_1hS,[_1mU,_1mZ,_1n2]))?[0,_1n1,_1n2]:[0,_1mY,_1mZ];default:return [0,_1n1,_1n2];}},_1n3=function(_1n4,_1n5){return [0,_1n4,function(_bt,_bu){return new F(function(){return _1mA(_1n4,_1n5,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1m8(_1n4,_1n5,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1mt(_1n4,_1n5,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1mm(_1n4,_1n5,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1mf(_1n4,_1n5,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1mH(_1n4,_1n5,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1mS(_1n4,_1n5,_bt,_bu);});}];},_1n6=function(_1n7,_1n8){return B(_w3(_1n7,_1n8))==0?false:true;},_1n9=function(_1na){return E(E(_1na)[1]);},_1nb=function(_1nc,_1nd){while(1){var _1ne=(function(_1nf,_1ng){var _1nh=E(_1ng);if(!_1nh[0]){_1nc=[1,_1nh[2],new T(function(){return B(_1nb(_1nf,_1nh[4]));})];_1nd=_1nh[3];return null;}else{return E(_1nf);}})(_1nc,_1nd);if(_1ne!=null){return _1ne;}}},_1ni=function(_1nj){return new F(function(){return _1nb(_f,_1nj);});},_1nk=function(_1nl){return function(_1nm,_1nn){var _1no=E(_1nm),_1np=E(_1nn);switch(B(_1hw(new T(function(){return B(_1n3(new T(function(){return B(_br(new T(function(){return B(_1n9(_1nl));})));}),_1nl));}),B(_1ni(_1no[1])),B(_1ni(_1np[1]))))){case 0:return false;case 1:return new F(function(){return _1n6(_1no[2],_1np[2]);});break;default:return true;}};},_1nq=new T(function(){return B(_1nk(_1m7));}),_1nr=function(_1ns,_1nt,_1nu){var _1nv=E(_1ns);if(_1nv==1){var _1nw=E(_1nu);return _1nw[0]==0?[0,new T(function(){return [0,1,E(E(_1nt)),E(_qh),E(_qh)];}),_f,_f]:!B(A(_1nq,[_1nt,_1nw[1]]))?[0,new T(function(){return [0,1,E(E(_1nt)),E(_qh),E(_qh)];}),_1nw,_f]:[0,new T(function(){return [0,1,E(E(_1nt)),E(_qh),E(_qh)];}),_f,_1nw];}else{var _1nx=B(_1nr(_1nv>>1,_1nt,_1nu)),_1ny=_1nx[1],_1nz=_1nx[3],_1nA=E(_1nx[2]);if(!_1nA[0]){return [0,_1ny,_f,_1nz];}else{var _1nB=_1nA[1],_1nC=E(_1nA[2]);if(!_1nC[0]){return [0,new T(function(){return B(_rE(_1nB,_1ny));}),_f,_1nz];}else{var _1nD=_1nC[1];if(!B(A(_1nq,[_1nB,_1nD]))){var _1nE=B(_1nr(_1nv>>1,_1nD,_1nC[2]));return [0,new T(function(){return B(_si(_1nB,_1ny,_1nE[1]));}),_1nE[2],_1nE[3]];}else{return [0,_1ny,_f,_1nA];}}}}},_1nF=function(_1nG,_1nH){return B(_w3(_1nG,_1nH))==2?false:true;},_1nI=function(_1nJ){return function(_1nK,_1nL){var _1nM=E(_1nK),_1nN=E(_1nL);switch(B(_1hw(new T(function(){return B(_1n3(new T(function(){return B(_br(new T(function(){return B(_1n9(_1nJ));})));}),_1nJ));}),B(_1ni(_1nM[1])),B(_1ni(_1nN[1]))))){case 0:return true;case 1:return new F(function(){return _1nF(_1nM[2],_1nN[2]);});break;default:return false;}};},_1nO=function(_1nP,_1nQ,_1nR,_1nS){return !B(A(_1nI,[_1nQ,_1nR,_1nS]))?E(_1nR):E(_1nS);},_1nT=function(_1nU,_1nV,_1nW,_1nX){return !B(A(_1nI,[_1nV,_1nW,_1nX]))?E(_1nX):E(_1nW);},_1nY=function(_1nZ,_1o0){return B(_w3(_1nZ,_1o0))==0?true:false;},_1o1=function(_1o2){return function(_1o3,_1o4){var _1o5=E(_1o3),_1o6=E(_1o4);switch(B(_1hw(new T(function(){return B(_1n3(new T(function(){return B(_br(new T(function(){return B(_1n9(_1o2));})));}),_1o2));}),B(_1ni(_1o5[1])),B(_1ni(_1o6[1]))))){case 0:return true;case 1:return new F(function(){return _1nY(_1o5[2],_1o6[2]);});break;default:return false;}};},_1o7=function(_1o8,_1o9){return B(_w3(_1o8,_1o9))==2?true:false;},_1oa=function(_1ob){return function(_1oc,_1od){var _1oe=E(_1oc),_1of=E(_1od);switch(B(_1hw(new T(function(){return B(_1n3(new T(function(){return B(_br(new T(function(){return B(_1n9(_1ob));})));}),_1ob));}),B(_1ni(_1oe[1])),B(_1ni(_1of[1]))))){case 0:return false;case 1:return new F(function(){return _1o7(_1oe[2],_1of[2]);});break;default:return true;}};},_1og=function(_1oh){return function(_1oi,_1oj){var _1ok=E(_1oi),_1ol=E(_1oj);switch(B(_1hw(new T(function(){return B(_1n3(new T(function(){return B(_br(new T(function(){return B(_1n9(_1oh));})));}),_1oh));}),B(_1ni(_1ok[1])),B(_1ni(_1ol[1]))))){case 0:return 0;case 1:return new F(function(){return _w3(_1ok[2],_1ol[2]);});break;default:return 2;}};},_1om=function(_1on,_1oo){return [0,_1on,new T(function(){return B(_1og(_1oo));}),new T(function(){return B(_1o1(_1oo));}),new T(function(){return B(_1nk(_1oo));}),new T(function(){return B(_1oa(_1oo));}),new T(function(){return B(_1nI(_1oo));}),function(_bt,_bu){return new F(function(){return _1nO(_1on,_1oo,_bt,_bu);});},function(_bt,_bu){return new F(function(){return _1nT(_1on,_1oo,_bt,_bu);});}];},_1op=function(_1oq,_1or,_1os){var _1ot=function(_1ou){var _1ov=function(_1ow){if(_1ou!=_1ow){return false;}else{return new F(function(){return _b3(_1oq,B(_1nb(_f,_1or)),B(_1nb(_f,_1os)));});}},_1ox=E(_1os);return _1ox[0]==0?B(_1ov(_1ox[1])):B(_1ov(0));},_1oy=E(_1or);return _1oy[0]==0?B(_1ot(_1oy[1])):B(_1ot(0));},_1oz=function(_1oA,_1oB,_1oC,_1oD,_1oE){return !B(_1op(new T(function(){return B(_br(_1oA));}),_1oB,_1oD))?true:!B(_bv(_1oC,_1oE))?true:false;},_1oF=function(_1oG,_1oH,_1oI){var _1oJ=E(_1oH),_1oK=E(_1oI);return new F(function(){return _1oz(_1oG,_1oJ[1],_1oJ[2],_1oK[1],_1oK[2]);});},_1oL=function(_1oM){return function(_1oN,_1oO){var _1oP=E(_1oN),_1oQ=E(_1oO);return !B(_1op(new T(function(){return B(_br(_1oM));}),_1oP[1],_1oQ[1]))?false:B(_bv(_1oP[2],_1oQ[2]));};},_1oR=function(_1oS){return [0,new T(function(){return B(_1oL(_1oS));}),function(_bt,_bu){return new F(function(){return _1oF(_1oS,_bt,_bu);});}];},_1oT=new T(function(){return B(_1oR(_1m6));}),_1oU=new T(function(){return B(_1om(_1oT,_1m7));}),_1oV=function(_1oW,_1oX,_1oY){var _1oZ=E(_1oX),_1p0=E(_1oY);if(!_1p0[0]){var _1p1=_1p0[2],_1p2=_1p0[3],_1p3=_1p0[4];switch(B(A(_1hu,[_1oW,_1oZ,_1p1]))){case 0:return new F(function(){return _qm(_1p1,B(_1oV(_1oW,_1oZ,_1p2)),_1p3);});break;case 1:return [0,_1p0[1],E(_1oZ),E(_1p2),E(_1p3)];default:return new F(function(){return _qY(_1p1,_1p2,B(_1oV(_1oW,_1oZ,_1p3)));});}}else{return [0,1,E(_1oZ),E(_qh),E(_qh)];}},_1p4=function(_1p5,_1p6){while(1){var _1p7=E(_1p6);if(!_1p7[0]){return E(_1p5);}else{var _1p8=B(_1oV(_1oU,_1p7[1],_1p5));_1p6=_1p7[2];_1p5=_1p8;continue;}}},_1p9=function(_1pa,_1pb,_1pc){return new F(function(){return _1p4(B(_1oV(_1oU,_1pb,_1pa)),_1pc);});},_1pd=function(_1pe,_1pf,_1pg){while(1){var _1ph=E(_1pg);if(!_1ph[0]){return E(_1pf);}else{var _1pi=_1ph[1],_1pj=E(_1ph[2]);if(!_1pj[0]){return new F(function(){return _rE(_1pi,_1pf);});}else{var _1pk=_1pj[1];if(!B(A(_1nq,[_1pi,_1pk]))){var _1pl=B(_1nr(_1pe,_1pk,_1pj[2])),_1pm=_1pl[1],_1pn=E(_1pl[3]);if(!_1pn[0]){var _1po=_1pe<<1,_1pp=B(_si(_1pi,_1pf,_1pm));_1pg=_1pl[2];_1pe=_1po;_1pf=_1pp;continue;}else{return new F(function(){return _1p9(B(_si(_1pi,_1pf,_1pm)),_1pn[1],_1pn[2]);});}}else{return new F(function(){return _1p9(_1pf,_1pi,_1pj);});}}}}},_1pq=function(_1pr,_1ps,_1pt,_1pu){var _1pv=E(_1pu);if(!_1pv[0]){return new F(function(){return _rE(_1pt,_1ps);});}else{var _1pw=_1pv[1];if(!B(A(_1nq,[_1pt,_1pw]))){var _1px=B(_1nr(_1pr,_1pw,_1pv[2])),_1py=_1px[1],_1pz=E(_1px[3]);if(!_1pz[0]){return new F(function(){return _1pd(_1pr<<1,B(_si(_1pt,_1ps,_1py)),_1px[2]);});}else{return new F(function(){return _1p9(B(_si(_1pt,_1ps,_1py)),_1pz[1],_1pz[2]);});}}else{return new F(function(){return _1p9(_1ps,_1pt,_1pv);});}}},_1pA=function(_1pB){var _1pC=E(_1pB);if(!_1pC[0]){return [1];}else{var _1pD=_1pC[1],_1pE=E(_1pC[2]);if(!_1pE[0]){return [0,1,E(E(_1pD)),E(_qh),E(_qh)];}else{var _1pF=_1pE[1],_1pG=_1pE[2];if(!B(A(_1nq,[_1pD,_1pF]))){return new F(function(){return _1pq(1,[0,1,E(E(_1pD)),E(_qh),E(_qh)],_1pF,_1pG);});}else{return new F(function(){return _1p9([0,1,E(E(_1pD)),E(_qh),E(_qh)],_1pF,_1pG);});}}}},_1pH=new T(function(){return B(_1ll(_6x,_6o,_6x,_6x,_6u,_6M,_61));}),_1pI=function(_1pJ,_1pK,_1pL,_1pM,_1pN){var _1pO=E(_1pJ);if(_1pO==1){var _1pP=E(_1pN);if(!_1pP[0]){return [0,[0,1,E([0,_1pK,[0,_1pL,_1pM]]),E(_qh),E(_qh)],_f,_f];}else{var _1pQ=E(_1pP[1]);switch(B(_1hw(_1m7,_1pK,_1pQ[1]))){case 0:return [0,[0,1,E([0,_1pK,[0,_1pL,_1pM]]),E(_qh),E(_qh)],_1pP,_f];case 1:var _1pR=E(_1pQ[2]);switch(B(_1hw(_1m5,_1pL,_1pR[1]))){case 0:return [0,[0,1,E([0,_1pK,[0,_1pL,_1pM]]),E(_qh),E(_qh)],_1pP,_f];case 1:return !B(A(_1pH,[_1pM,_1pR[2]]))?[0,[0,1,E([0,_1pK,[0,_1pL,_1pM]]),E(_qh),E(_qh)],_1pP,_f]:[0,[0,1,E([0,_1pK,[0,_1pL,_1pM]]),E(_qh),E(_qh)],_f,_1pP];default:return [0,[0,1,E([0,_1pK,[0,_1pL,_1pM]]),E(_qh),E(_qh)],_f,_1pP];}break;default:return [0,[0,1,E([0,_1pK,[0,_1pL,_1pM]]),E(_qh),E(_qh)],_f,_1pP];}}}else{var _1pS=B(_1pI(_1pO>>1,_1pK,_1pL,_1pM,_1pN)),_1pT=_1pS[1],_1pU=_1pS[3],_1pV=E(_1pS[2]);if(!_1pV[0]){return [0,_1pT,_f,_1pU];}else{var _1pW=_1pV[1],_1pX=E(_1pV[2]);if(!_1pX[0]){return [0,new T(function(){return B(_rE(_1pW,_1pT));}),_f,_1pU];}else{var _1pY=_1pX[2],_1pZ=E(_1pW),_1q0=E(_1pX[1]),_1q1=_1q0[1],_1q2=_1q0[2];switch(B(_1hw(_1m7,_1pZ[1],_1q1))){case 0:var _1q3=B(_1q4(_1pO>>1,_1q1,_1q2,_1pY));return [0,new T(function(){return B(_si(_1pZ,_1pT,_1q3[1]));}),_1q3[2],_1q3[3]];case 1:var _1q5=E(_1pZ[2]),_1q6=E(_1q2),_1q7=_1q6[1],_1q8=_1q6[2];switch(B(_1hw(_1m5,_1q5[1],_1q7))){case 0:var _1q9=B(_1pI(_1pO>>1,_1q1,_1q7,_1q8,_1pY));return [0,new T(function(){return B(_si(_1pZ,_1pT,_1q9[1]));}),_1q9[2],_1q9[3]];case 1:if(!B(A(_1pH,[_1q5[2],_1q8]))){var _1qa=B(_1pI(_1pO>>1,_1q1,_1q7,_1q8,_1pY));return [0,new T(function(){return B(_si(_1pZ,_1pT,_1qa[1]));}),_1qa[2],_1qa[3]];}else{return [0,_1pT,_f,_1pV];}break;default:return [0,_1pT,_f,_1pV];}break;default:return [0,_1pT,_f,_1pV];}}}}},_1q4=function(_1qb,_1qc,_1qd,_1qe){var _1qf=E(_1qb);if(_1qf==1){var _1qg=E(_1qe);if(!_1qg[0]){return [0,[0,1,E([0,_1qc,_1qd]),E(_qh),E(_qh)],_f,_f];}else{var _1qh=E(_1qg[1]);switch(B(_1hw(_1m7,_1qc,_1qh[1]))){case 0:return [0,[0,1,E([0,_1qc,_1qd]),E(_qh),E(_qh)],_1qg,_f];case 1:var _1qi=E(_1qd),_1qj=E(_1qh[2]);switch(B(_1hw(_1m5,_1qi[1],_1qj[1]))){case 0:return [0,[0,1,E([0,_1qc,_1qi]),E(_qh),E(_qh)],_1qg,_f];case 1:return !B(A(_1pH,[_1qi[2],_1qj[2]]))?[0,[0,1,E([0,_1qc,_1qi]),E(_qh),E(_qh)],_1qg,_f]:[0,[0,1,E([0,_1qc,_1qi]),E(_qh),E(_qh)],_f,_1qg];default:return [0,[0,1,E([0,_1qc,_1qi]),E(_qh),E(_qh)],_f,_1qg];}break;default:return [0,[0,1,E([0,_1qc,_1qd]),E(_qh),E(_qh)],_f,_1qg];}}}else{var _1qk=B(_1q4(_1qf>>1,_1qc,_1qd,_1qe)),_1ql=_1qk[1],_1qm=_1qk[3],_1qn=E(_1qk[2]);if(!_1qn[0]){return [0,_1ql,_f,_1qm];}else{var _1qo=_1qn[1],_1qp=E(_1qn[2]);if(!_1qp[0]){return [0,new T(function(){return B(_rE(_1qo,_1ql));}),_f,_1qm];}else{var _1qq=_1qp[2],_1qr=E(_1qo),_1qs=E(_1qp[1]),_1qt=_1qs[1],_1qu=_1qs[2];switch(B(_1hw(_1m7,_1qr[1],_1qt))){case 0:var _1qv=B(_1q4(_1qf>>1,_1qt,_1qu,_1qq));return [0,new T(function(){return B(_si(_1qr,_1ql,_1qv[1]));}),_1qv[2],_1qv[3]];case 1:var _1qw=E(_1qr[2]),_1qx=E(_1qu),_1qy=_1qx[1],_1qz=_1qx[2];switch(B(_1hw(_1m5,_1qw[1],_1qy))){case 0:var _1qA=B(_1pI(_1qf>>1,_1qt,_1qy,_1qz,_1qq));return [0,new T(function(){return B(_si(_1qr,_1ql,_1qA[1]));}),_1qA[2],_1qA[3]];case 1:if(!B(A(_1pH,[_1qw[2],_1qz]))){var _1qB=B(_1pI(_1qf>>1,_1qt,_1qy,_1qz,_1qq));return [0,new T(function(){return B(_si(_1qr,_1ql,_1qB[1]));}),_1qB[2],_1qB[3]];}else{return [0,_1ql,_f,_1qn];}break;default:return [0,_1ql,_f,_1qn];}break;default:return [0,_1ql,_f,_1qn];}}}}},_1qC=new T(function(){return B(_1lD(_6x,_6o,_6x,_6x,_6u,_6M,_61));}),_1qD=function(_1qE,_1qF,_1qG,_1qH){var _1qI=E(_1qH);if(!_1qI[0]){var _1qJ=_1qI[3],_1qK=_1qI[4],_1qL=E(_1qI[2]);switch(B(_1hw(_1m7,_1qE,_1qL[1]))){case 0:return new F(function(){return _qm(_1qL,B(_1qD(_1qE,_1qF,_1qG,_1qJ)),_1qK);});break;case 1:var _1qM=E(_1qL[2]);switch(B(_1hw(_1m5,_1qF,_1qM[1]))){case 0:return new F(function(){return _qm(_1qL,B(_1qD(_1qE,_1qF,_1qG,_1qJ)),_1qK);});break;case 1:switch(B(A(_1qC,[_1qG,_1qM[2]]))){case 0:return new F(function(){return _qm(_1qL,B(_1qD(_1qE,_1qF,_1qG,_1qJ)),_1qK);});break;case 1:return [0,_1qI[1],E([0,_1qE,[0,_1qF,_1qG]]),E(_1qJ),E(_1qK)];default:return new F(function(){return _qY(_1qL,_1qJ,B(_1qD(_1qE,_1qF,_1qG,_1qK)));});}break;default:return new F(function(){return _qY(_1qL,_1qJ,B(_1qD(_1qE,_1qF,_1qG,_1qK)));});}break;default:return new F(function(){return _qY(_1qL,_1qJ,B(_1qD(_1qE,_1qF,_1qG,_1qK)));});}}else{return [0,1,E([0,_1qE,[0,_1qF,_1qG]]),E(_qh),E(_qh)];}},_1qN=function(_1qO,_1qP,_1qQ){var _1qR=E(_1qQ);if(!_1qR[0]){var _1qS=_1qR[3],_1qT=_1qR[4],_1qU=E(_1qR[2]);switch(B(_1hw(_1m7,_1qO,_1qU[1]))){case 0:return new F(function(){return _qm(_1qU,B(_1qN(_1qO,_1qP,_1qS)),_1qT);});break;case 1:var _1qV=E(_1qP),_1qW=_1qV[1],_1qX=_1qV[2],_1qY=E(_1qU[2]);switch(B(_1hw(_1m5,_1qW,_1qY[1]))){case 0:return new F(function(){return _qm(_1qU,B(_1qD(_1qO,_1qW,_1qX,_1qS)),_1qT);});break;case 1:switch(B(A(_1qC,[_1qX,_1qY[2]]))){case 0:return new F(function(){return _qm(_1qU,B(_1qD(_1qO,_1qW,_1qX,_1qS)),_1qT);});break;case 1:return [0,_1qR[1],E([0,_1qO,_1qV]),E(_1qS),E(_1qT)];default:return new F(function(){return _qY(_1qU,_1qS,B(_1qD(_1qO,_1qW,_1qX,_1qT)));});}break;default:return new F(function(){return _qY(_1qU,_1qS,B(_1qD(_1qO,_1qW,_1qX,_1qT)));});}break;default:return new F(function(){return _qY(_1qU,_1qS,B(_1qN(_1qO,_1qP,_1qT)));});}}else{return [0,1,E([0,_1qO,_1qP]),E(_qh),E(_qh)];}},_1qZ=function(_1r0,_1r1){while(1){var _1r2=E(_1r1);if(!_1r2[0]){return E(_1r0);}else{var _1r3=E(_1r2[1]),_1r4=B(_1qN(_1r3[1],_1r3[2],_1r0));_1r1=_1r2[2];_1r0=_1r4;continue;}}},_1r5=function(_1r6,_1r7,_1r8,_1r9){return new F(function(){return _1qZ(B(_1qN(_1r7,_1r8,_1r6)),_1r9);});},_1ra=function(_1rb,_1rc,_1rd){var _1re=E(_1rc);return new F(function(){return _1qZ(B(_1qN(_1re[1],_1re[2],_1rb)),_1rd);});},_1rf=function(_1rg,_1rh,_1ri){var _1rj=E(_1ri);if(!_1rj[0]){return E(_1rh);}else{var _1rk=_1rj[1],_1rl=E(_1rj[2]);if(!_1rl[0]){return new F(function(){return _rE(_1rk,_1rh);});}else{var _1rm=E(_1rk),_1rn=_1rm[1],_1ro=_1rm[2],_1rp=E(_1rl[1]),_1rq=_1rp[1],_1rr=_1rp[2],_1rs=function(_1rt){var _1ru=B(_1q4(_1rg,_1rq,_1rr,_1rl[2])),_1rv=_1ru[1],_1rw=E(_1ru[3]);if(!_1rw[0]){return new F(function(){return _1rf(_1rg<<1,B(_si(_1rm,_1rh,_1rv)),_1ru[2]);});}else{return new F(function(){return _1ra(B(_si(_1rm,_1rh,_1rv)),_1rw[1],_1rw[2]);});}};switch(B(_1hw(_1m7,_1rn,_1rq))){case 0:return new F(function(){return _1rs(_);});break;case 1:var _1rx=E(_1ro),_1ry=E(_1rr);switch(B(_1hw(_1m5,_1rx[1],_1ry[1]))){case 0:return new F(function(){return _1rs(_);});break;case 1:return !B(A(_1pH,[_1rx[2],_1ry[2]]))?B(_1rs(_)):B(_1r5(_1rh,_1rn,_1rx,_1rl));default:return new F(function(){return _1r5(_1rh,_1rn,_1rx,_1rl);});}break;default:return new F(function(){return _1r5(_1rh,_1rn,_1ro,_1rl);});}}}},_1rz=function(_1rA,_1rB,_1rC,_1rD,_1rE,_1rF){var _1rG=E(_1rF);if(!_1rG[0]){return new F(function(){return _rE([0,_1rC,[0,_1rD,_1rE]],_1rB);});}else{var _1rH=E(_1rG[1]),_1rI=_1rH[1],_1rJ=_1rH[2],_1rK=function(_1rL){var _1rM=B(_1q4(_1rA,_1rI,_1rJ,_1rG[2])),_1rN=_1rM[1],_1rO=E(_1rM[3]);if(!_1rO[0]){return new F(function(){return _1rf(_1rA<<1,B(_si([0,_1rC,[0,_1rD,_1rE]],_1rB,_1rN)),_1rM[2]);});}else{return new F(function(){return _1ra(B(_si([0,_1rC,[0,_1rD,_1rE]],_1rB,_1rN)),_1rO[1],_1rO[2]);});}};switch(B(_1hw(_1m7,_1rC,_1rI))){case 0:return new F(function(){return _1rK(_);});break;case 1:var _1rP=E(_1rJ);switch(B(_1hw(_1m5,_1rD,_1rP[1]))){case 0:return new F(function(){return _1rK(_);});break;case 1:return !B(A(_1pH,[_1rE,_1rP[2]]))?B(_1rK(_)):B(_1r5(_1rB,_1rC,[0,_1rD,_1rE],_1rG));default:return new F(function(){return _1r5(_1rB,_1rC,[0,_1rD,_1rE],_1rG);});}break;default:return new F(function(){return _1r5(_1rB,_1rC,[0,_1rD,_1rE],_1rG);});}}},_1rQ=function(_1rR,_1rS,_1rT,_1rU,_1rV){var _1rW=E(_1rV);if(!_1rW[0]){return new F(function(){return _rE([0,_1rT,_1rU],_1rS);});}else{var _1rX=E(_1rW[1]),_1rY=_1rX[1],_1rZ=_1rX[2],_1s0=function(_1s1){var _1s2=B(_1q4(_1rR,_1rY,_1rZ,_1rW[2])),_1s3=_1s2[1],_1s4=E(_1s2[3]);if(!_1s4[0]){return new F(function(){return _1rf(_1rR<<1,B(_si([0,_1rT,_1rU],_1rS,_1s3)),_1s2[2]);});}else{return new F(function(){return _1ra(B(_si([0,_1rT,_1rU],_1rS,_1s3)),_1s4[1],_1s4[2]);});}};switch(B(_1hw(_1m7,_1rT,_1rY))){case 0:return new F(function(){return _1s0(_);});break;case 1:var _1s5=E(_1rU),_1s6=E(_1rZ);switch(B(_1hw(_1m5,_1s5[1],_1s6[1]))){case 0:return new F(function(){return _1s0(_);});break;case 1:return !B(A(_1pH,[_1s5[2],_1s6[2]]))?B(_1s0(_)):B(_1r5(_1rS,_1rT,_1s5,_1rW));default:return new F(function(){return _1r5(_1rS,_1rT,_1s5,_1rW);});}break;default:return new F(function(){return _1r5(_1rS,_1rT,_1rU,_1rW);});}}},_1s7=function(_1s8){var _1s9=E(_1s8);if(!_1s9[0]){return [1];}else{var _1sa=_1s9[1],_1sb=E(_1s9[2]);if(!_1sb[0]){return [0,1,E(E(_1sa)),E(_qh),E(_qh)];}else{var _1sc=_1sb[2],_1sd=E(_1sa),_1se=E(_1sb[1]),_1sf=_1se[1],_1sg=_1se[2];switch(B(_1hw(_1m7,_1sd[1],_1sf))){case 0:return new F(function(){return _1rQ(1,[0,1,E(_1sd),E(_qh),E(_qh)],_1sf,_1sg,_1sc);});break;case 1:var _1sh=E(_1sd[2]),_1si=E(_1sg),_1sj=_1si[1],_1sk=_1si[2];switch(B(_1hw(_1m5,_1sh[1],_1sj))){case 0:return new F(function(){return _1rz(1,[0,1,E(_1sd),E(_qh),E(_qh)],_1sf,_1sj,_1sk,_1sc);});break;case 1:return !B(A(_1pH,[_1sh[2],_1sk]))?B(_1rz(1,[0,1,E(_1sd),E(_qh),E(_qh)],_1sf,_1sj,_1sk,_1sc)):B(_1r5([0,1,E(_1sd),E(_qh),E(_qh)],_1sf,_1si,_1sc));default:return new F(function(){return _1r5([0,1,E(_1sd),E(_qh),E(_qh)],_1sf,_1si,_1sc);});}break;default:return new F(function(){return _1r5([0,1,E(_1sd),E(_qh),E(_qh)],_1sf,_1sg,_1sc);});}}}},_1sl=new T(function(){return B(_4e(0,1,_f));}),_1sm=new T(function(){return B(unAppCStr("delta_",_1sl));}),_1sn=[9,_,_,_1sm],_1so=[0,_1sn],_1sp=[1,_1so,_f],_1sq=new T(function(){return B(unAppCStr("phi_",_1sl));}),_1sr=[3,_,_,_1sq],_1ss=[2,_,_1sr],_1st=[1,_1ss,_f],_1su=[1,_1st],_1sv=[0,_1sp,_1su],_1sw=new T(function(){return B(_4e(0,2,_f));}),_1sx=new T(function(){return B(unAppCStr("phi_",_1sw));}),_1sy=[3,_,_,_1sx],_1sz=[2,_,_1sy],_1sA=[1,_1sz,_f],_1sB=[1,_1sA],_1sC=new T(function(){return B(unAppCStr("delta_",_1sw));}),_1sD=[9,_,_,_1sC],_1sE=[0,_1sD],_1sF=[1,_1sE,_f],_1sG=[0,_1sF,_1sB],_1sH=[1,_1sG,_f],_1sI=[1,_1sv,_1sH],_1sJ=[9,_,_190,_1ss,_1sz],_1sK=[1,_1sJ,_f],_1sL=[1,_1sK],_1sM=[1,_1so,_1sF],_1sN=[0,_1sM,_1sL],_1sO=[0,_1sI,_1sN],_1sP=[0,_1sF,_1su],_1sQ=[1,_1sP,_f],_1sR=[0,_1sp,_1sB],_1sS=[1,_1sR,_1sQ],_1sT=[0,_1sS,_1sN],_1sU=[1,_1sT,_f],_1sV=[1,_1sO,_1sU],_1sW=new T(function(){return B(_1s7(_1sV));}),_1sX=[0,_1sW,_1hc],_1sY=[1,_1sv,_f],_1sZ=[9,_,_18C,_1ss,_1sz],_1t0=[1,_1sZ,_f],_1t1=[1,_1t0],_1t2=[0,_1sp,_1t1],_1t3=[0,_1sY,_1t2],_1t4=[9,_,_18C,_1sz,_1ss],_1t5=[1,_1t4,_f],_1t6=[1,_1t5],_1t7=[0,_1sp,_1t6],_1t8=[0,_1sY,_1t7],_1t9=[1,_1t8,_f],_1ta=[1,_1t3,_1t9],_1tb=new T(function(){return B(_1s7(_1ta));}),_1tc=[0,_1tb,_1hb],_1td=[7,_,_19r,_1sz],_1te=[1,_1td,_f],_1tf=[1,_1te],_1tg=[1,_1su,_1sF],_1th=[0,_1tg,_1tf],_1ti=[1,_1th,_f],_1tj=[1,_1su,_1sp],_1tk=[0,_1tj,_1sB],_1tl=[1,_1tk,_1ti],_1tm=[7,_,_19r,_1ss],_1tn=[1,_1tm,_f],_1to=[1,_1tn],_1tp=[0,_1sM,_1to],_1tq=[0,_1tl,_1tp],_1tr=[1,_1sR,_1ti],_1ts=[0,_1tr,_1tp],_1tt=[0,_1sF,_1tf],_1tu=[1,_1tt,_f],_1tv=[1,_1tk,_1tu],_1tw=[0,_1tv,_1tp],_1tx=[1,_1sR,_1tu],_1ty=[0,_1tx,_1tp],_1tz=[1,_1tk,_f],_1tA=[1,_1th,_1tz],_1tB=[0,_1tA,_1tp],_1tC=[1,_1tt,_1tz],_1tD=[0,_1tC,_1tp],_1tE=[1,_1sR,_f],_1tF=[1,_1th,_1tE],_1tG=[0,_1tF,_1tp],_1tH=[1,_1tt,_1tE],_1tI=[0,_1tH,_1tp],_1tJ=[1,_1tI,_f],_1tK=[1,_1tG,_1tJ],_1tL=[1,_1tD,_1tK],_1tM=[1,_1tB,_1tL],_1tN=[1,_1ty,_1tM],_1tO=[1,_1tw,_1tN],_1tP=[1,_1ts,_1tO],_1tQ=[1,_1tq,_1tP],_1tR=new T(function(){return B(_1s7(_1tQ));}),_1tS=[0,_1tR,_1hi],_1tT=[1,_1tS,_f],_1tU=[1,_1tc,_1tT],_1tV=[0,83],_1tW=[1,_1tV,_f],_1tX=[0,_1sp,_1sL],_1tY=[1,_1tX,_f],_1tZ=[0,_1tY,_1sv],_1u0=[0,_1tY,_1sR],_1u1=[1,_1u0,_f],_1u2=[1,_1tZ,_1u1],_1u3=new T(function(){return B(_1s7(_1u2));}),_1u4=[0,_1u3,_1tW],_1u5=[1,_1u4,_1tU],_1u6=[0,_1sM,_1sB],_1u7=[0,_1sF,_1to],_1u8=[1,_1u7,_f],_1u9=[1,_1t7,_1u8],_1ua=[0,_1u9,_1u6],_1ub=[1,_1t7,_f],_1uc=[1,_1u7,_1ub],_1ud=[0,_1uc,_1u6],_1ue=[1,_1ua,_f],_1uf=[1,_1ud,_1ue],_1ug=[1,_1ua,_1uf],_1uh=[1,_1ua,_1ug],_1ui=new T(function(){return B(_1s7(_1uh));}),_1uj=[0,_1ui,_1hg],_1uk=[1,_1uj,_1u5],_1ul=[9,_,_17q,_1ss,_1sz],_1um=[1,_1ul,_f],_1un=[1,_1um],_1uo=[0,_1sF,_1un],_1up=[1,_1uo,_f],_1uq=[1,_1sv,_1up],_1ur=[0,_1uq,_1u6],_1us=[0,_1sp,_1un],_1ut=[1,_1us,_1sQ],_1uu=[0,_1ut,_1u6],_1uv=[1,_1uu,_f],_1uw=[1,_1ur,_1uv],_1ux=new T(function(){return B(_1s7(_1uw));}),_1uy=[0,_1ux,_1hh],_1uz=[1,_1uy,_1uk],_1uA=[0,_1tE,_1us],_1uB=[0,_1tz,_1us],_1uC=[1,_1uB,_f],_1uD=[1,_1uA,_1uC],_1uE=new T(function(){return B(_1s7(_1uD));}),_1uF=[0,_1uE,_1hj],_1uG=[1,_1uF,_1uz],_1uH=[1,_1sX,_1uG],_1uI=new T(function(){return B(_1pA(_1uH));}),_1uJ=function(_1uK){return new F(function(){return _wq(_1uK,_f);});},_1uL=function(_1uM,_1uN){return _1uM<=B(_iW(_1uN,0))?[1,new T(function(){var _1uO=_1uM-1|0;if(_1uO>=0){var _1uP=B(_zE(B(_1uJ(_1uN)),_1uO));}else{var _1uP=E(_zB);}var _1uQ=_1uP,_1uR=_1uQ;return _1uR;})]:[0];},_1uS=function(_1uT,_1uU,_1uV){var _1uW=function(_1uX){return _1uX<=B(_iW(_1uV,0))?[1,[0,new T(function(){var _1uY=_1uT-1|0;if(_1uY>=0){var _1uZ=B(_zE(B(_1uJ(_1uV)),_1uY));}else{var _1uZ=E(_zB);}var _1v0=_1uZ,_1v1=_1v0;return _1v1;}),new T(function(){var _1v2=_1uU-1|0;if(_1v2>=0){var _1v3=B(_zE(B(_1uJ(_1uV)),_1v2));}else{var _1v3=E(_zB);}var _1v4=_1v3,_1v5=_1v4;return _1v5;})]]:[0];};return _1uT>_1uU?B(_1uW(_1uT)):B(_1uW(_1uU));},_1v6=[0],_1v7=new T(function(){return B(unCStr("depends on unjustified lines"));}),_1v8=new T(function(){return B(unCStr("unavailable lines"));}),_1v9=new T(function(){return B(unCStr("wrong number of premises"));}),_1va=new T(function(){return B(unCStr("Impossible Error 1"));}),_1vb=new T(function(){return B(unCStr("Not an assertion-justifying rule"));}),_1vc=new T(function(){return B(unCStr("PR"));}),_1vd=new T(function(){return B(unCStr("Unrecognized Inference Rule"));}),_1ve=function(_1vf,_1vg,_1vh,_1vi,_1vj,_1vk){var _1vl=function(_1vm){var _1vn=B(A(_1vi,[_1vg]));if(!_1vn[0]){return [0,[1,_1vd,_1vj],[1,_Z,_1vk]];}else{var _1vo=E(_1vn[1]);if(!_1vo[0]){switch(E(E(_1vo[1])[1])){case 1:var _1vp=E(_1vh);if(!_1vp[0]){return [0,[1,_1v9,_1vj],[1,_Z,_1vk]];}else{if(!E(_1vp[2])[0]){var _1vq=B(_1uL(E(_1vp[1])[1],_1vk));if(!_1vq[0]){return [0,[1,_1v8,_1vj],[1,_Z,_1vk]];}else{var _1vr=E(_1vq[1]);return _1vr[0]==0?[0,[1,_1v7,_1vj],[1,_Z,_1vk]]:[0,[1,_f,_1vj],[1,[1,[0,_1vf,[1,_1vg,[1,_1vr[1],_f]]]],_1vk]];}}else{return [0,[1,_1v9,_1vj],[1,_Z,_1vk]];}}break;case 2:var _1vs=E(_1vh);if(!_1vs[0]){return [0,[1,_1v9,_1vj],[1,_Z,_1vk]];}else{var _1vt=E(_1vs[2]);if(!_1vt[0]){return [0,[1,_1v9,_1vj],[1,_Z,_1vk]];}else{if(!E(_1vt[2])[0]){var _1vu=B(_1uS(E(_1vs[1])[1],E(_1vt[1])[1],_1vk));if(!_1vu[0]){return [0,[1,_1v8,_1vj],[1,_Z,_1vk]];}else{var _1vv=E(_1vu[1]),_1vw=E(_1vv[1]);if(!_1vw[0]){return [0,[1,_1v7,_1vj],[1,_Z,_1vk]];}else{var _1vx=E(_1vv[2]);return _1vx[0]==0?[0,[1,_1v7,_1vj],[1,_Z,_1vk]]:[0,[1,_f,_1vj],[1,[1,[0,_1vf,[1,_1vg,[1,_1vw[1],[1,_1vx[1],_f]]]]],_1vk]];}}}else{return [0,[1,_1v9,_1vj],[1,_Z,_1vk]];}}}break;default:return [0,[1,_1va,_1vj],[1,_Z,_1vk]];}}else{return [0,[1,_1vb,_1vj],[1,_Z,_1vk]];}}};return !B(_bv(_1vg,_1vc))?B(_1vl(_)):E(_1vh)[0]==0?[0,[1,_f,_1vj],[1,[1,[0,_1vf,_1v6]],_1vk]]:B(_1vl(_));},_1vy=new T(function(){return B(unCStr("depends on an unjustified line"));}),_1vz=new T(function(){return B(unCStr("unavailable line"));}),_1vA=function(_1vB,_1vC,_1vD,_1vE){return E(B(_1vF(_1vB,_1vC,[1,_f,_1vD],[1,_Z,_1vE]))[2]);},_1vG=function(_1vH,_1vI,_1vJ,_1vK,_1vL,_1vM,_1vN,_1vO){var _1vP=B(_1uS(_1vK,_1vL,B(_1vA(_1vH,_1vI,_1vN,_1vO))));if(!_1vP[0]){return new F(function(){return _1vF(_1vH,_1vI,[1,_1vz,_1vN],[1,_Z,_1vO]);});}else{var _1vQ=E(_1vP[1]),_1vR=E(_1vQ[1]);if(!_1vR[0]){return new F(function(){return _1vF(_1vH,_1vI,[1,_1vy,_1vN],[1,_Z,_1vO]);});}else{var _1vS=E(_1vQ[2]);return _1vS[0]==0?B(_1vF(_1vH,_1vI,[1,_1vy,_1vN],[1,_Z,_1vO])):B(_1vF(_1vH,_1vI,[1,_f,_1vN],[1,[1,[0,_1vJ,[1,_1vM,[1,_1vR[1],[1,_1vS[1],_f]]]]],_1vO]));}}},_1vT=new T(function(){return B(unCStr("wrong number of lines cited"));}),_1vU=function(_1vV,_1vW,_1vX,_1vY,_1vZ,_1w0,_1w1){var _1w2=E(_1vZ);if(!_1w2[0]){return new F(function(){return _1vF(_1vV,_1vW,[1,_1vT,_1w0],[1,_Z,_1w1]);});}else{var _1w3=E(_1w2[2]);if(!_1w3[0]){return new F(function(){return _1vF(_1vV,_1vW,[1,_1vT,_1w0],[1,_Z,_1w1]);});}else{if(!E(_1w3[2])[0]){return new F(function(){return _1vG(_1vV,_1vW,_1vX,E(_1w2[1])[1],E(_1w3[1])[1],_1vY,_1w0,_1w1);});}else{return new F(function(){return _1vF(_1vV,_1vW,[1,_1vT,_1w0],[1,_Z,_1w1]);});}}}},_1w4=function(_1w5,_1w6,_1w7){return [0,_1w6,new T(function(){var _1w8=B(_iW(_1w6,0))-E(_1w5)[1]|0,_1w9=new T(function(){return _1w8>=0?B(_nB(_1w8,_1w7)):E(_1w7);});if(_1w8>0){var _1wa=function(_1wb,_1wc){var _1wd=E(_1wb);return _1wd[0]==0?E(_1w9):_1wc>1?[1,_Z,new T(function(){return B(_1wa(_1wd[2],_1wc-1|0));})]:E([1,_Z,_1w9]);},_1we=B(_1wa(_1w7,_1w8));}else{var _1we=E(_1w9);}var _1wf=_1we,_1wg=_1wf,_1wh=_1wg,_1wi=_1wh;return _1wi;})];},_1wj=function(_1wk,_1wl,_1wm,_1wn,_1wo,_1wp,_1wq){var _1wr=new T(function(){return E(B(_1vF(_1wk,_1wl,[1,_f,_1wp],[1,_Z,_1wq]))[2]);});if(_1wn<=B(_iW(_1wr,0))){var _1ws=_1wn-1|0;if(_1ws>=0){var _1wt=B(_zE(B(_1uJ(_1wr)),_1ws));return _1wt[0]==0?B(_1vF(_1wk,_1wl,[1,_1vy,_1wp],[1,_Z,_1wq])):B(_1vF(_1wk,_1wl,[1,_f,_1wp],[1,[1,[0,_1wm,[1,_1wo,[1,_1wt[1],_f]]]],_1wq]));}else{return E(_zB);}}else{return new F(function(){return _1vF(_1wk,_1wl,[1,_1vz,_1wp],[1,_Z,_1wq]);});}},_1wu=function(_1wv,_1ww,_1wx,_1wy,_1wz,_1wA,_1wB){var _1wC=E(_1wz);if(!_1wC[0]){return new F(function(){return _1vF(_1wv,_1ww,[1,_1vT,_1wA],[1,_Z,_1wB]);});}else{if(!E(_1wC[2])[0]){return new F(function(){return _1wj(_1wv,_1ww,_1wx,E(_1wC[1])[1],_1wy,_1wA,_1wB);});}else{return new F(function(){return _1vF(_1wv,_1ww,[1,_1vT,_1wA],[1,_Z,_1wB]);});}}},_1wD=new T(function(){return B(unCStr("Open Subproof"));}),_1wE=new T(function(){return B(unCStr("Impossible Error 2"));}),_1wF=new T(function(){return B(unCStr("Not a derivation-closing rule"));}),_1wG=new T(function(){return B(unCStr("SHOW"));}),_1wH=function(_1wI,_1wJ,_1wK,_1wL,_1wM,_1wN,_1wO){if(!B(_bv(_1wJ,_1wG))){var _1wP=B(A(_1wL,[_1wJ]));if(!_1wP[0]){return [0,[1,_1vd,_1wN],[1,_Z,_1wO]];}else{var _1wQ=E(_1wP[1]);if(!_1wQ[0]){return [0,[1,_1wF,_1wN],[1,_Z,_1wO]];}else{switch(E(E(_1wQ[1])[1])){case 1:var _1wR=B(_1wu(_1wM,_1wL,_1wI,_1wJ,_1wK,_1wN,_1wO));return new F(function(){return _1w4(new T(function(){return [0,B(_iW(_1wN,0))+1|0];},1),_1wR[1],_1wR[2]);});break;case 2:var _1wS=B(_1vU(_1wM,_1wL,_1wI,_1wJ,_1wK,_1wN,_1wO));return new F(function(){return _1w4(new T(function(){return [0,B(_iW(_1wN,0))+1|0];},1),_1wS[1],_1wS[2]);});break;default:return [0,[1,_1wE,_1wN],[1,_Z,_1wO]];}}}}else{var _1wT=B(_1vF(_1wM,_1wL,[1,_1wD,_1wN],[1,_Z,_1wO]));return new F(function(){return _1w4(new T(function(){return [0,B(_iW(_1wN,0))+1|0];},1),_1wT[1],_1wT[2]);});}},_1wU=new T(function(){return B(unCStr("shouldn\'t happen"));}),_1wV=new T(function(){return B(unCStr("formula syntax error"));}),_1wW=function(_1wX,_1wY,_1wZ,_1x0,_1x1){var _1x2=E(_1wX);if(!_1x2[0]){return E(_1wY)[0]==0?[0,[1,_1wV,_1x0],[1,_Z,_1x1]]:[0,[1,_1wU,_1x0],[1,_Z,_1x1]];}else{var _1x3=_1x2[1],_1x4=E(_1wY);if(!_1x4[0]){var _1x5=E(_1x3);return new F(function(){return _1ve(_1x5[1],_1x5[2],_1x5[3],_1wZ,_1x0,_1x1);});}else{var _1x6=E(_1x3);return new F(function(){return _1wH(_1x6[1],_1x6[2],_1x6[3],_1wZ,_1x4,_1x0,_1x1);});}}},_1vF=function(_1x7,_1x8,_1x9,_1xa){return new F(function(){return (function(_1xb,_1xc,_1xd){while(1){var _1xe=E(_1xd);if(!_1xe[0]){return [0,_1xb,_1xc];}else{var _1xf=E(_1xe[1]),_1xg=B(_1wW(_1xf[1],_1xf[2],_1x8,_1xb,_1xc));_1xb=_1xg[1];_1xc=_1xg[2];_1xd=_1xe[2];continue;}}})(_1x9,_1xa,_1x7);});},_1xh=function(_1xi,_1xj){while(1){var _1xk=E(_1xj);if(!_1xk[0]){return true;}else{if(!B(A(_1xi,[_1xk[1]]))){return false;}else{_1xj=_1xk[2];continue;}}}},_1xl=[0,666],_1xm=[0,_,_1xl],_1xn=[1,_1xm],_1xo=[0,_1xn,_1v6],_1xp=function(_1xq){return new F(function(){return _bv(_1xq,_f);});},_1xr=function(_1xs,_1xt){var _1xu=B(_1vF(_1xs,_1xt,_f,_f)),_1xv=_1xu[1];return !B(_1xh(_1xp,_1xv))?[0,_1xv]:[1,new T(function(){var _1xw=B(_iW(_1xs,0))-1|0;if(_1xw>=0){var _1xx=B(_zE(B(_wq(_1xu[2],_f)),_1xw)),_1xy=_1xx[0]==0?E(_1xo):E(_1xx[1]);}else{var _1xy=E(_zB);}var _1xz=_1xy,_1xA=_1xz,_1xB=_1xA;return _1xB;})];},_1xC=function(_1xD,_1xE){return E(_60);},_1xF=function(_1xG,_1xH,_1xI,_1xJ){var _1xK=E(_1xI);switch(_1xK[0]){case 0:var _1xL=E(_1xJ);return _1xL[0]==0?E(_60):E(_1xL[1]);case 1:return new F(function(){return A(_1xG,[_1xK[1],_f]);});break;case 2:return new F(function(){return A(_1xH,[_1xK[1],[1,new T(function(){return B(_1xF(_1xG,_1xH,_1xK[2],_1xJ));}),_f]]);});break;default:return new F(function(){return A(_1xH,[_1xK[1],[1,new T(function(){return B(_1xF(_1xG,_1xH,_1xK[2],_1xJ));}),[1,new T(function(){return B(_1xF(_1xG,_1xH,_1xK[3],_1xJ));}),_f]]]);});}},_1xM=function(_1xN,_1xO,_1xP,_1xQ,_1xR,_1xS,_1xT,_1xU){var _1xV=E(_1xT);switch(_1xV[0]){case 0:return [0];case 1:return new F(function(){return A(_1xQ,[_1xV[1],_f]);});break;case 2:return new F(function(){return A(_1xN,[_1xV[1],[1,new T(function(){return B(_1xF(_1xQ,_1xR,_1xV[2],_1xU));}),_f]]);});break;case 3:return new F(function(){return A(_1xN,[_1xV[1],[1,new T(function(){return B(_1xF(_1xQ,_1xR,_1xV[2],_1xU));}),[1,new T(function(){return B(_1xF(_1xQ,_1xR,_1xV[3],_1xU));}),_f]]]);});break;case 4:return new F(function(){return A(_1xO,[_1xV[1],[1,new T(function(){return B(_1xM(_1xN,_1xO,_1xP,_1xQ,_1xR,_1xS,_1xV[2],_1xU));}),_f]]);});break;case 5:return new F(function(){return A(_1xO,[_1xV[1],[1,new T(function(){return B(_1xM(_1xN,_1xO,_1xP,_1xQ,_1xR,_1xS,_1xV[2],_1xU));}),[1,new T(function(){return B(_1xM(_1xN,_1xO,_1xP,_1xQ,_1xR,_1xS,_1xV[3],_1xU));}),_f]]]);});break;default:var _1xW=_1xV[1],_1xX=_1xV[2];return new F(function(){return A(_1xP,[_1xW,[1,new T(function(){return B(A(_1xS,[new T(function(){return B(A(_1xX,[_am]));}),_1xW]));}),[1,new T(function(){return B(_1xM(_1xN,_1xO,_1xP,_1xQ,_1xR,_1xS,B(A(_1xX,[_am])),[1,new T(function(){return B(A(_1xS,[new T(function(){return B(A(_1xX,[_am]));}),_1xW]));}),_f]));}),_f]]]);});}},_1xY=[0,95],_1xZ=[1,_1xY,_f],_1y0=[1,_1xZ,_f],_1y1=function(_1y2,_){return _1y2;},_1y3=function(_1y4){var _1y5=E(_1y4);return _1y5[0]==0?E(_1y1):function(_1y6,_){var _1y7=B(A(new T(function(){var _1y8=E(_1y5[1]);return B(_1y9(_1y8[1],_1y8[2]));}),[_1y6,_])),_1ya=_1y7,_1yb=B(A(new T(function(){return B(_1y3(_1y5[2]));}),[_1y6,_])),_1yc=_1yb;return _1y6;};},_1yd=function(_1ye,_1yf){return function(_1yg,_){var _1yh=B(A(new T(function(){var _1yi=E(_1ye);return B(_1y9(_1yi[1],_1yi[2]));}),[_1yg,_])),_1yj=_1yh,_1yk=B(A(new T(function(){return B(_1y3(_1yf));}),[_1yg,_])),_1yl=_1yk;return _1yg;};},_1ym=function(_1yn,_1yo){return new F(function(){return _4e(0,E(_1yn)[1],_1yo);});},_1yp=function(_1yq){return function(_lZ,_m0){return new F(function(){return _5T(new T(function(){return B(_1O(_1ym,_1yq,_f));}),_lZ,_m0);});};},_1yr=function(_1ys){return function(_lZ,_m0){return new F(function(){return _5T(new T(function(){return B(_1xM(_6x,_6o,_6x,_6u,_6x,_1xC,_1ys,_1y0));}),_lZ,_m0);});};},_1yt=new T(function(){return B(unCStr("open"));}),_1yu=new T(function(){return B(unCStr("termination"));}),_1yv=new T(function(){return B(unCStr("closed"));}),_1yw=new T(function(){return B(unCStr("class"));}),_1yx=function(_1yy){var _1yz=E(_1yy);return _1yz[0]==0?E(_1y1):function(_1yA,_){var _1yB=B(A(new T(function(){var _1yC=E(_1yz[1]);return B(_1y9(_1yC[1],_1yC[2]));}),[_1yA,_])),_1yD=_1yB,_1yE=B(A(new T(function(){return B(_1yx(_1yz[2]));}),[_1yA,_])),_1yF=_1yE;return _1yA;};},_1yG=function(_1yH,_1yI){return function(_1yJ,_){var _1yK=B(A(new T(function(){var _1yL=E(_1yH);return B(_1y9(_1yL[1],_1yL[2]));}),[_1yJ,_])),_1yM=_1yK,_1yN=B(A(new T(function(){return B(_1yx(_1yI));}),[_1yJ,_])),_1yO=_1yN;return _1yJ;};},_1yP=new T(function(){return B(unCStr("SHOW"));}),_1y9=function(_1yQ,_1yR){var _1yS=E(_1yQ);if(!_1yS[0]){return function(_lZ,_m0){return new F(function(){return _vB(_5T,_1yS[1],_lZ,_m0);});};}else{var _1yT=E(_1yS[1]),_1yU=_1yT[1],_1yV=_1yT[2],_1yW=_1yT[3];if(!B(_bv(_1yV,_1yP))){var _1yX=E(_1yR);return _1yX[0]==0?function(_lZ,_m0){return new F(function(){return _vB(_54,function(_1yY,_){var _1yZ=B(_4U(_1yr,_1yU,_1yY,_)),_1z0=_1yZ,_1z1=B(_4U(_54,function(_1z2,_){var _1z3=B(_4U(_5T,_1yV,_1z2,_)),_1z4=_1z3,_1z5=B(_4U(_1yp,_1yW,_1z2,_)),_1z6=_1z5;return _1z2;},_1yY,_)),_1z7=_1z1;return _1yY;},_lZ,_m0);});}:function(_lZ,_m0){return new F(function(){return _vB(_54,function(_1z8,_){var _1z9=B(_4U(_5T,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1xM(_6x,_6o,_6x,_6u,_6x,_1xC,_1yU,_1y0));})));}),_1z8,_)),_1za=_1z9,_1zb=B(_vB(_54,function(_1zc,_){var _1zd=B(_4U(_54,new T(function(){return B(_1yd(_1yX[1],_1yX[2]));}),_1zc,_)),_1ze=_1zd,_1zf=B(_vB(_54,function(_1zg,_){var _1zh=B(_4U(_5T,_f,_1zg,_)),_1zi=_1zh,_1zj=B(A(_41,[_4r,_1zi,_1yw,_1yu,_])),_1zk=_1zj,_1zl=B(_4U(_54,function(_1zm,_){var _1zn=B(_4U(_5T,_1yV,_1zm,_)),_1zo=_1zn,_1zp=B(_4U(_1yp,_1yW,_1zm,_)),_1zq=_1zp;return _1zm;},_1zg,_)),_1zr=_1zl;return _1zg;},_1zc,_)),_1zs=_1zf;return _1zc;},_1z8,_)),_1zt=_1zb,_1zu=B(A(_41,[_4r,_1zt,_1yw,_1yv,_])),_1zv=_1zu;return _1z8;},_lZ,_m0);});};}else{var _1zw=E(_1yR);return _1zw[0]==0?function(_lZ,_m0){return new F(function(){return _vB(_54,function(_uV,_){return new F(function(){return _4U(_5T,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1xM(_6x,_6o,_6x,_6u,_6x,_1xC,_1yU,_1y0));})));}),_uV,_);});},_lZ,_m0);});}:function(_lZ,_m0){return new F(function(){return _vB(_54,function(_1zx,_){var _1zy=B(_4U(_5T,new T(function(){return B(unAppCStr("Show: ",new T(function(){return B(_1xM(_6x,_6o,_6x,_6u,_6x,_1xC,_1yU,_1y0));})));}),_1zx,_)),_1zz=_1zy,_1zA=B(_vB(_54,function(_uV,_){return new F(function(){return _4U(_54,new T(function(){return B(_1yG(_1zw[1],_1zw[2]));}),_uV,_);});},_1zx,_)),_1zB=_1zA,_1zC=B(A(_41,[_4r,_1zB,_1yw,_1yt,_])),_1zD=_1zC;return _1zx;},_lZ,_m0);});};}}},_1zE=function(_1zF){var _1zG=E(_1zF);return _1zG[0]==0?E(_1y1):function(_1zH,_){var _1zI=B(A(new T(function(){var _1zJ=E(_1zG[1]);return B(_1y9(_1zJ[1],_1zJ[2]));}),[_1zH,_])),_1zK=_1zI,_1zL=B(A(new T(function(){return B(_1zE(_1zG[2]));}),[_1zH,_])),_1zM=_1zL;return _1zH;};},_1zN=[0,10],_1zO=[1,_1zN,_f],_1zP=function(_1zQ){var _1zR=new T(function(){var _1zS=B(_Xi(_Wa,_XE,[0,new T(function(){return B(_1E(_1zQ,_1zO));}),E(_W5),E(_0)]));if(!_1zS[0]){var _1zT=E(_1zS[1]);if(!_1zT[0]){var _1zU=E(E(_1zT[1])[1]);}else{var _1zU=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9S(_1zT[1]));})));})],_f],_f];}var _1zV=_1zU;}else{var _1zW=E(_1zS[1]);if(!_1zW[0]){var _1zX=E(E(_1zW[1])[1]);}else{var _1zX=[1,[0,[0,new T(function(){return B(unAppCStr("pair error",new T(function(){return B(_9S(_1zW[1]));})));})],_f],_f];}var _1zV=_1zX;}return _1zV;});return function(_lZ,_m0){return new F(function(){return _56(_w0,function(_1zY,_1zZ,_){return new F(function(){return _56(function(_1A0,_){return [0,[0,function(_1A1,_){var _1A2=B(_4U(_54,new T(function(){return B(_1zE(_1zR));}),_1A1,_)),_1A3=_1A2,_1A4=B(A(_41,[_4r,_1A3,_4q,_w2,_])),_1A5=_1A4;return _1A3;},_uW],_1A0];},function(_1A6){return E(new T(function(){var _1A7=B(_1xr(_1zR,_1hr));if(!_1A7[0]){var _1A8=function(_1A9,_){return [0,[0,function(_1Aa,_){var _1Ab=B(_vB(_54,function(_uV,_){return new F(function(){return _vL(new T(function(){return B(_wq(_1A7[1],_f));}),_uV,_);});},_1Aa,_)),_1Ac=_1Ab,_1Ad=B(A(_41,[_4r,_1Ac,_4q,_uS,_])),_1Ae=_1Ad;return _1Ac;},_uW],_1A9];};}else{var _1Af=E(_1A7[1]),_1Ag=B(_uu(_61,_6M,_6u,_6x,_6x,_6o,_6x,_6I,_a2,_9W,_a5,_1uI,_1Af[1],_1Af[2]));if(!_1Ag[0]){var _1Ah=E(_vz);}else{var _1Ah=function(_lZ,_m0){return new F(function(){return _v2(_v0,_uR,function(_1Ai,_){return [0,[0,function(_uV,_){return new F(function(){return _4U(_5T,new T(function(){var _1Aj=E(_1Ag[1]);return B(_aY(_1Aj[1],_1Aj[2]));}),_uV,_);});},_uW],_1Ai];},_lZ,_m0);});};}var _1Ak=_1Ah,_1A8=_1Ak;}return _1A8;}));},_1zZ,_);});},_lZ,_m0);});};},_1Al=new T(function(){return B(unCStr("lined"));}),_1Am=function(_1An,_1Ao,_){var _1Ap=jsCreateElem(toJSStr(E(_1An))),_1Aq=_1Ap,_1Ar=jsAppendChild(_1Aq,E(_1Ao)[1]);return [0,_1Aq];},_1As=function(_1At,_1Au,_1Av,_){var _1Aw=B(_1Am(_1At,_1Av,_)),_1Ax=_1Aw,_1Ay=B(A(_1Au,[_1Ax,_])),_1Az=_1Ay;return _1Ax;},_1AA=new T(function(){return B(unCStr("()"));}),_1AB=new T(function(){return B(unCStr("GHC.Tuple"));}),_1AC=new T(function(){return B(unCStr("ghc-prim"));}),_1AD=new T(function(){var _1AE=hs_wordToWord64(2170319554),_1AF=_1AE,_1AG=hs_wordToWord64(26914641),_1AH=_1AG;return [0,_1AF,_1AH,[0,_1AF,_1AH,_1AC,_1AB,_1AA],_f];}),_1AI=function(_1AJ){return E(_1AD);},_1AK=new T(function(){return B(unCStr("PerchM"));}),_1AL=new T(function(){return B(unCStr("Haste.Perch"));}),_1AM=new T(function(){return B(unCStr("haste-perch-0.1.0.7"));}),_1AN=new T(function(){var _1AO=hs_wordToWord64(3005229400),_1AP=_1AO,_1AQ=hs_wordToWord64(2682402736),_1AR=_1AQ;return [0,_1AP,_1AR,[0,_1AP,_1AR,_1AM,_1AL,_1AK],_f];}),_1AS=function(_1AT){return E(_1AN);},_1AU=function(_1AV){var _1AW=E(_1AV);if(!_1AW[0]){return [0];}else{var _1AX=E(_1AW[1]);return [1,[0,_1AX[1],_1AX[2]],new T(function(){return B(_1AU(_1AW[2]));})];}},_1AY=function(_1AZ,_1B0){var _1B1=E(_1AZ);if(!_1B1){return [0,_f,_1B0];}else{var _1B2=E(_1B0);if(!_1B2[0]){return [0,_f,_f];}else{var _1B3=new T(function(){var _1B4=B(_1AY(_1B1-1|0,_1B2[2]));return [0,_1B4[1],_1B4[2]];});return [0,[1,_1B2[1],new T(function(){return E(E(_1B3)[1]);})],new T(function(){return E(E(_1B3)[2]);})];}}},_1B5=[0,120],_1B6=[0,48],_1B7=function(_1B8){var _1B9=new T(function(){var _1Ba=B(_1AY(8,new T(function(){var _1Bb=md5(toJSStr(E(_1B8))),_1Bc=_1Bb;return fromJSStr(_1Bc);})));return [0,_1Ba[1],_1Ba[2]];}),_1Bd=parseInt([0,toJSStr([1,_1B6,[1,_1B5,new T(function(){return E(E(_1B9)[1]);})]])]),_1Be=_1Bd,_1Bf=new T(function(){var _1Bg=B(_1AY(8,new T(function(){return E(E(_1B9)[2]);})));return [0,_1Bg[1],_1Bg[2]];}),_1Bh=parseInt([0,toJSStr([1,_1B6,[1,_1B5,new T(function(){return E(E(_1Bf)[1]);})]])]),_1Bi=_1Bh,_1Bj=hs_mkWord64(_1Be,_1Bi),_1Bk=_1Bj,_1Bl=parseInt([0,toJSStr([1,_1B6,[1,_1B5,new T(function(){return E(B(_1AY(8,new T(function(){return E(E(_1Bf)[2]);})))[1]);})]])]),_1Bm=_1Bl,_1Bn=hs_mkWord64(_1Bm,_1Bm),_1Bo=_1Bn;return [0,_1Bk,_1Bo];},_1Bp=function(_1Bq,_1Br){var _1Bs=jsShowI(_1Bq),_1Bt=_1Bs,_1Bu=md5(_1Bt),_1Bv=_1Bu;return new F(function(){return _1E(fromJSStr(_1Bv),new T(function(){var _1Bw=jsShowI(_1Br),_1Bx=_1Bw,_1By=md5(_1Bx),_1Bz=_1By;return fromJSStr(_1Bz);},1));});},_1BA=function(_1BB){var _1BC=E(_1BB);return new F(function(){return _1Bp(_1BC[1],_1BC[2]);});},_1BD=function(_1BE,_1BF){return function(_1BG){return E(new T(function(){var _1BH=B(A(_1BE,[_])),_1BI=E(_1BH[3]),_1BJ=_1BI[1],_1BK=_1BI[2],_1BL=B(_1E(_1BH[4],[1,new T(function(){return B(A(_1BF,[_]));}),_f]));if(!_1BL[0]){var _1BM=[0,_1BJ,_1BK,_1BI,_f];}else{var _1BN=B(_1B7(new T(function(){return B(_7n(B(_7T(_1BA,[1,[0,_1BJ,_1BK],new T(function(){return B(_1AU(_1BL));})]))));},1))),_1BM=[0,_1BN[1],_1BN[2],_1BI,_1BL];}var _1BO=_1BM,_1BP=_1BO;return _1BP;}));};},_1BQ=new T(function(){return B(_1BD(_1AS,_1AI));}),_1BR=function(_1BS,_1BT,_1BU,_){var _1BV=E(_1BT),_1BW=B(A(_1BS,[_1BU,_])),_1BX=_1BW,_1BY=B(A(_41,[_4r,_1BX,_1BV[1],_1BV[2],_])),_1BZ=_1BY;return _1BX;},_1C0=function(_1C1,_1C2){while(1){var _1C3=(function(_1C4,_1C5){var _1C6=E(_1C5);if(!_1C6[0]){return E(_1C4);}else{_1C1=function(_1C7,_){return new F(function(){return _1BR(_1C4,_1C6[1],_1C7,_);});};_1C2=_1C6[2];return null;}})(_1C1,_1C2);if(_1C3!=null){return _1C3;}}},_1C8=new T(function(){return B(unCStr("value"));}),_1C9=new T(function(){return B(unCStr("id"));}),_1Ca=new T(function(){return B(unCStr("onclick"));}),_1Cb=new T(function(){return B(unCStr("checked"));}),_1Cc=[0,_1Cb,_f],_1Cd=[1,_1Cc,_f],_1Ce=new T(function(){return B(unCStr("type"));}),_1Cf=new T(function(){return B(unCStr("input"));}),_1Cg=function(_1Ch,_){return new F(function(){return _1Am(_1Cf,_1Ch,_);});},_1Ci=function(_1Cj,_1Ck,_1Cl,_1Cm,_1Cn){var _1Co=new T(function(){var _1Cp=new T(function(){return B(_1C0(_1Cg,[1,[0,_1Ce,_1Ck],[1,[0,_1C9,_1Cj],[1,[0,_1C8,_1Cl],_f]]]));});return !E(_1Cm)?E(_1Cp):B(_1C0(_1Cp,_1Cd));}),_1Cq=E(_1Cn);return _1Cq[0]==0?E(_1Co):B(_1C0(_1Co,[1,[0,_1Ca,_1Cq[1]],_f]));},_1Cr=new T(function(){return B(unCStr("href"));}),_1Cs=[0,97],_1Ct=[1,_1Cs,_f],_1Cu=function(_1Cv,_){return new F(function(){return _1Am(_1Ct,_1Cv,_);});},_1Cw=function(_1Cx,_1Cy){return function(_1Cz,_){var _1CA=B(A(new T(function(){return B(_1C0(_1Cu,[1,[0,_1Cr,_1Cx],_f]));}),[_1Cz,_])),_1CB=_1CA,_1CC=B(A(_1Cy,[_1CB,_])),_1CD=_1CC;return _1CB;};},_1CE=function(_1CF){return new F(function(){return _1Cw(_1CF,function(_1C7,_){return new F(function(){return _5T(_1CF,_1C7,_);});});});},_1CG=new T(function(){return B(unCStr("option"));}),_1CH=function(_1CI,_){return new F(function(){return _1Am(_1CG,_1CI,_);});},_1CJ=new T(function(){return B(unCStr("selected"));}),_1CK=[0,_1CJ,_f],_1CL=[1,_1CK,_f],_1CM=function(_1CN,_1CO,_1CP){var _1CQ=new T(function(){return B(_1C0(_1CH,[1,[0,_1C8,_1CN],_f]));});if(!E(_1CP)){return function(_1CR,_){var _1CS=B(A(_1CQ,[_1CR,_])),_1CT=_1CS,_1CU=B(A(_1CO,[_1CT,_])),_1CV=_1CU;return _1CT;};}else{return new F(function(){return _1C0(function(_1CW,_){var _1CX=B(A(_1CQ,[_1CW,_])),_1CY=_1CX,_1CZ=B(A(_1CO,[_1CY,_])),_1D0=_1CZ;return _1CY;},_1CL);});}},_1D1=function(_1D2,_1D3){return new F(function(){return _1CM(_1D2,function(_1C7,_){return new F(function(){return _5T(_1D2,_1C7,_);});},_1D3);});},_1D4=new T(function(){return B(unCStr("method"));}),_1D5=new T(function(){return B(unCStr("action"));}),_1D6=new T(function(){return B(unCStr("UTF-8"));}),_1D7=new T(function(){return B(unCStr("acceptCharset"));}),_1D8=[0,_1D7,_1D6],_1D9=new T(function(){return B(unCStr("form"));}),_1Da=function(_1Db,_){return new F(function(){return _1Am(_1D9,_1Db,_);});},_1Dc=function(_1Dd,_1De,_1Df){return function(_1Dg,_){var _1Dh=B(A(new T(function(){return B(_1C0(_1Da,[1,_1D8,[1,[0,_1D5,_1Dd],[1,[0,_1D4,_1De],_f]]]));}),[_1Dg,_])),_1Di=_1Dh,_1Dj=B(A(_1Df,[_1Di,_])),_1Dk=_1Dj;return _1Di;};},_1Dl=new T(function(){return B(unCStr("select"));}),_1Dm=function(_1Dn,_){return new F(function(){return _1Am(_1Dl,_1Dn,_);});},_1Do=function(_1Dp,_1Dq){return function(_1Dr,_){var _1Ds=B(A(new T(function(){return B(_1C0(_1Dm,[1,[0,_1C9,_1Dp],_f]));}),[_1Dr,_])),_1Dt=_1Ds,_1Du=B(A(_1Dq,[_1Dt,_])),_1Dv=_1Du;return _1Dt;};},_1Dw=new T(function(){return B(unCStr("textarea"));}),_1Dx=function(_1Dy,_){return new F(function(){return _1Am(_1Dw,_1Dy,_);});},_1Dz=function(_1DA,_1DB){return function(_1DC,_){var _1DD=B(A(new T(function(){return B(_1C0(_1Dx,[1,[0,_1C9,_1DA],_f]));}),[_1DC,_])),_1DE=_1DD,_1DF=B(_5T(_1DB,_1DE,_)),_1DG=_1DF;return _1DE;};},_1DH=new T(function(){return B(unCStr("color:red"));}),_1DI=new T(function(){return B(unCStr("style"));}),_1DJ=[0,_1DI,_1DH],_1DK=[1,_1DJ,_f],_1DL=[0,98],_1DM=[1,_1DL,_f],_1DN=function(_1DO){return new F(function(){return _1C0(function(_1DP,_){var _1DQ=B(_1Am(_1DM,_1DP,_)),_1DR=_1DQ,_1DS=B(A(_1DO,[_1DR,_])),_1DT=_1DS;return _1DR;},_1DK);});},_1DU=function(_1DV,_1DW,_){var _1DX=E(_1DV);if(!_1DX[0]){return _1DW;}else{var _1DY=B(A(_1DX[1],[_1DW,_])),_1DZ=_1DY,_1E0=B(_1DU(_1DX[2],_1DW,_)),_1E1=_1E0;return _1DW;}},_1E2=function(_1E3,_1E4,_){return new F(function(){return _1DU(_1E3,_1E4,_);});},_1E5=function(_1E6,_1E7,_1E8,_){var _1E9=B(A(_1E6,[_1E8,_])),_1Ea=_1E9,_1Eb=B(A(_1E7,[_1E8,_])),_1Ec=_1Eb;return _1E8;},_1Ed=[0,_4u,_1E5,_1E2],_1Ee=[0,_1Ed,_1BQ,_5T,_5T,_1As,_1DN,_1Cw,_1CE,_1Ci,_1Dz,_1Do,_1CM,_1D1,_1Dc,_1C0],_1Ef=function(_1Eg,_1Eh,_){var _1Ei=B(A(_1Eh,[_])),_1Ej=_1Ei;return _1Eg;},_1Ek=function(_1El,_1Em,_){var _1En=B(A(_1Em,[_])),_1Eo=_1En;return new T(function(){return B(A(_1El,[_1Eo]));});},_1Ep=[0,_1Ek,_1Ef],_1Eq=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1Er=new T(function(){return B(unCStr("base"));}),_1Es=new T(function(){return B(unCStr("IOException"));}),_1Et=new T(function(){var _1Eu=hs_wordToWord64(4053623282),_1Ev=_1Eu,_1Ew=hs_wordToWord64(3693590983),_1Ex=_1Ew;return [0,_1Ev,_1Ex,[0,_1Ev,_1Ex,_1Er,_1Eq,_1Es],_f];}),_1Ey=function(_1Ez){return E(_1Et);},_1EA=function(_1EB){var _1EC=E(_1EB);return new F(function(){return _1p(B(_1n(_1EC[1])),_1Ey,_1EC[2]);});},_1ED=new T(function(){return B(unCStr(": "));}),_1EE=[0,41],_1EF=new T(function(){return B(unCStr(" ("));}),_1EG=new T(function(){return B(unCStr("already exists"));}),_1EH=new T(function(){return B(unCStr("does not exist"));}),_1EI=new T(function(){return B(unCStr("protocol error"));}),_1EJ=new T(function(){return B(unCStr("failed"));}),_1EK=new T(function(){return B(unCStr("invalid argument"));}),_1EL=new T(function(){return B(unCStr("inappropriate type"));}),_1EM=new T(function(){return B(unCStr("hardware fault"));}),_1EN=new T(function(){return B(unCStr("unsupported operation"));}),_1EO=new T(function(){return B(unCStr("timeout"));}),_1EP=new T(function(){return B(unCStr("resource vanished"));}),_1EQ=new T(function(){return B(unCStr("interrupted"));}),_1ER=new T(function(){return B(unCStr("resource busy"));}),_1ES=new T(function(){return B(unCStr("resource exhausted"));}),_1ET=new T(function(){return B(unCStr("end of file"));}),_1EU=new T(function(){return B(unCStr("illegal operation"));}),_1EV=new T(function(){return B(unCStr("permission denied"));}),_1EW=new T(function(){return B(unCStr("user error"));}),_1EX=new T(function(){return B(unCStr("unsatisified constraints"));}),_1EY=new T(function(){return B(unCStr("system error"));}),_1EZ=function(_1F0,_1F1){switch(E(_1F0)){case 0:return new F(function(){return _1E(_1EG,_1F1);});break;case 1:return new F(function(){return _1E(_1EH,_1F1);});break;case 2:return new F(function(){return _1E(_1ER,_1F1);});break;case 3:return new F(function(){return _1E(_1ES,_1F1);});break;case 4:return new F(function(){return _1E(_1ET,_1F1);});break;case 5:return new F(function(){return _1E(_1EU,_1F1);});break;case 6:return new F(function(){return _1E(_1EV,_1F1);});break;case 7:return new F(function(){return _1E(_1EW,_1F1);});break;case 8:return new F(function(){return _1E(_1EX,_1F1);});break;case 9:return new F(function(){return _1E(_1EY,_1F1);});break;case 10:return new F(function(){return _1E(_1EI,_1F1);});break;case 11:return new F(function(){return _1E(_1EJ,_1F1);});break;case 12:return new F(function(){return _1E(_1EK,_1F1);});break;case 13:return new F(function(){return _1E(_1EL,_1F1);});break;case 14:return new F(function(){return _1E(_1EM,_1F1);});break;case 15:return new F(function(){return _1E(_1EN,_1F1);});break;case 16:return new F(function(){return _1E(_1EO,_1F1);});break;case 17:return new F(function(){return _1E(_1EP,_1F1);});break;default:return new F(function(){return _1E(_1EQ,_1F1);});}},_1F2=[0,125],_1F3=new T(function(){return B(unCStr("{handle: "));}),_1F4=function(_1F5,_1F6,_1F7,_1F8,_1F9,_1Fa){var _1Fb=new T(function(){var _1Fc=new T(function(){return B(_1EZ(_1F6,new T(function(){var _1Fd=E(_1F8);return _1Fd[0]==0?E(_1Fa):B(_1E(_1EF,new T(function(){return B(_1E(_1Fd,[1,_1EE,_1Fa]));},1)));},1)));},1),_1Fe=E(_1F7);return _1Fe[0]==0?E(_1Fc):B(_1E(_1Fe,new T(function(){return B(_1E(_1ED,_1Fc));},1)));},1),_1Ff=E(_1F9);if(!_1Ff[0]){var _1Fg=E(_1F5);if(!_1Fg[0]){return E(_1Fb);}else{var _1Fh=E(_1Fg[1]);return _1Fh[0]==0?B(_1E(_1F3,new T(function(){return B(_1E(_1Fh[1],[1,_1F2,new T(function(){return B(_1E(_1ED,_1Fb));})]));},1))):B(_1E(_1F3,new T(function(){return B(_1E(_1Fh[1],[1,_1F2,new T(function(){return B(_1E(_1ED,_1Fb));})]));},1)));}}else{return new F(function(){return _1E(_1Ff[1],new T(function(){return B(_1E(_1ED,_1Fb));},1));});}},_1Fi=function(_1Fj){var _1Fk=E(_1Fj);return new F(function(){return _1F4(_1Fk[1],_1Fk[2],_1Fk[3],_1Fk[4],_1Fk[6],_f);});},_1Fl=function(_1Fm,_1Fn){var _1Fo=E(_1Fm);return new F(function(){return _1F4(_1Fo[1],_1Fo[2],_1Fo[3],_1Fo[4],_1Fo[6],_1Fn);});},_1Fp=function(_1Fq,_1Fr){return new F(function(){return _1O(_1Fl,_1Fq,_1Fr);});},_1Fs=function(_1Ft,_1Fu,_1Fv){var _1Fw=E(_1Fu);return new F(function(){return _1F4(_1Fw[1],_1Fw[2],_1Fw[3],_1Fw[4],_1Fw[6],_1Fv);});},_1Fx=[0,_1Fs,_1Fi,_1Fp],_1Fy=new T(function(){return [0,_1Ey,_1Fx,_1Fz,_1EA];}),_1Fz=function(_1FA){return [0,_1Fy,_1FA];},_1FB=7,_1FC=function(_1FD){return [0,_Z,_1FB,_f,_1FD,_Z,_Z];},_1FE=function(_1FF,_){return new F(function(){return die(new T(function(){return B(_1Fz(new T(function(){return B(_1FC(_1FF));})));}));});},_1FG=function(_1FH,_){return new F(function(){return _1FE(_1FH,_);});},_1FI=function(_1FJ,_){return new F(function(){return _1FG(_1FJ,_);});},_1FK=function(_1FL,_){return new F(function(){return _1FI(_1FL,_);});},_1FM=function(_1FN,_1FO,_){var _1FP=B(A(_1FN,[_])),_1FQ=_1FP;return new F(function(){return A(_1FO,[_1FQ,_]);});},_1FR=function(_1FS,_1FT,_){var _1FU=B(A(_1FS,[_])),_1FV=_1FU;return new F(function(){return A(_1FT,[_]);});},_1FW=[0,_1FM,_1FR,_4u,_1FK],_1FX=[0,_1FW,_4r],_1FY=function(_1FZ){return E(E(_1FZ)[1]);},_1G0=function(_1G1){return E(E(_1G1)[2]);},_1G2=function(_1G3,_1G4){var _1G5=new T(function(){return B(_1FY(_1G3));});return function(_1G6){return new F(function(){return A(new T(function(){return B(_17G(_1G5));}),[new T(function(){return B(A(_1G0,[_1G3,_1G4]));}),function(_1G7){return new F(function(){return A(new T(function(){return B(_BZ(_1G5));}),[[0,_1G7,_1G6]]);});}]);});};},_1G8=function(_1G9,_1Ga){return [0,_1G9,function(_1Gb){return new F(function(){return _1G2(_1Ga,_1Gb);});}];},_1Gc=function(_1Gd,_1Ge,_1Gf,_1Gg){return new F(function(){return A(_17G,[_1Gd,new T(function(){return B(A(_1Ge,[_1Gg]));}),function(_1Gh){return new F(function(){return A(_1Gf,[new T(function(){return E(E(_1Gh)[1]);}),new T(function(){return E(E(_1Gh)[2]);})]);});}]);});},_1Gi=function(_1Gj,_1Gk,_1Gl,_1Gm){return new F(function(){return A(_17G,[_1Gj,new T(function(){return B(A(_1Gk,[_1Gm]));}),function(_1Gn){return new F(function(){return A(_1Gl,[new T(function(){return E(E(_1Gn)[2]);})]);});}]);});},_1Go=function(_1Gp,_1Gq,_1Gr,_1Gs){return new F(function(){return _1Gi(_1Gp,_1Gq,_1Gr,_1Gs);});},_1Gt=function(_1Gu){return E(E(_1Gu)[4]);},_1Gv=function(_1Gw,_1Gx){return function(_1Gy){return E(new T(function(){return B(A(_1Gt,[_1Gw,_1Gx]));}));};},_1Gz=function(_1GA){return [0,function(_1Gq,_1Gr,_1Gs){return new F(function(){return _1Gc(_1GA,_1Gq,_1Gr,_1Gs);});},function(_1Gq,_1Gr,_1Gs){return new F(function(){return _1Go(_1GA,_1Gq,_1Gr,_1Gs);});},function(_1GB,_1GC){return new F(function(){return A(new T(function(){return B(_BZ(_1GA));}),[[0,_1GB,_1GC]]);});},function(_1Gs){return new F(function(){return _1Gv(_1GA,_1Gs);});}];},_1GD=function(_1GE,_1GF,_1GG){return new F(function(){return A(_BZ,[_1GE,[0,_1GF,_1GG]]);});},_1GH=[0,10],_1GI=function(_1GJ,_1GK){var _1GL=E(_1GK);if(!_1GL[0]){return E(_4r);}else{var _1GM=_1GL[1],_1GN=E(_1GL[2]);if(!_1GN[0]){var _1GO=E(_1GM);return new F(function(){return _1GP(_1GH,_1GO[3],_1GO[4]);});}else{return function(_1GQ){return new F(function(){return A(new T(function(){var _1GR=E(_1GM);return B(_1GP(_1GH,_1GR[3],_1GR[4]));}),[new T(function(){return B(A(_1GJ,[new T(function(){return B(A(new T(function(){return B(_1GI(_1GJ,_1GN));}),[_1GQ]));})]));})]);});};}}},_1GS=new T(function(){return B(unCStr("(->)"));}),_1GT=new T(function(){return B(unCStr("GHC.Prim"));}),_1GU=new T(function(){var _1GV=hs_wordToWord64(4173248105),_1GW=_1GV,_1GX=hs_wordToWord64(4270398258),_1GY=_1GX;return [0,_1GW,_1GY,[0,_1GW,_1GY,_1AC,_1GT,_1GS],_f];}),_1GZ=new T(function(){return E(E(_1GU)[3]);}),_1H0=new T(function(){return B(unCStr("GHC.Types"));}),_1H1=new T(function(){return B(unCStr("[]"));}),_1H2=new T(function(){var _1H3=hs_wordToWord64(4033920485),_1H4=_1H3,_1H5=hs_wordToWord64(786266835),_1H6=_1H5;return [0,_1H4,_1H6,[0,_1H4,_1H6,_1AC,_1H0,_1H1],_f];}),_1H7=[1,_1AD,_f],_1H8=function(_1H9){var _1Ha=E(_1H9);if(!_1Ha[0]){return [0];}else{var _1Hb=E(_1Ha[1]);return [1,[0,_1Hb[1],_1Hb[2]],new T(function(){return B(_1H8(_1Ha[2]));})];}},_1Hc=new T(function(){var _1Hd=E(_1H2),_1He=E(_1Hd[3]),_1Hf=B(_1E(_1Hd[4],_1H7));if(!_1Hf[0]){var _1Hg=E(_1He);}else{var _1Hh=B(_1B7(new T(function(){return B(_7n(B(_7T(_1BA,[1,[0,_1He[1],_1He[2]],new T(function(){return B(_1H8(_1Hf));})]))));},1))),_1Hg=E(_1He);}var _1Hi=_1Hg,_1Hj=_1Hi;return _1Hj;}),_1Hk=[0,8],_1Hl=[0,32],_1Hm=function(_1Hn){return [1,_1Hl,_1Hn];},_1Ho=new T(function(){return B(unCStr(" -> "));}),_1Hp=[0,9],_1Hq=[0,93],_1Hr=[0,91],_1Hs=[0,41],_1Ht=[0,44],_1Hu=function(_1Hn){return [1,_1Ht,_1Hn];},_1Hv=[0,40],_1Hw=[0,0],_1GP=function(_1Hx,_1Hy,_1Hz){var _1HA=E(_1Hz);if(!_1HA[0]){return function(_1HB){return new F(function(){return _1E(E(_1Hy)[5],_1HB);});};}else{var _1HC=_1HA[1],_1HD=function(_1HE){var _1HF=E(_1Hy)[5],_1HG=function(_1HH){var _1HI=new T(function(){return B(_1GI(_1Hm,_1HA));});return E(_1Hx)[1]<=9?function(_1HJ){return new F(function(){return _1E(_1HF,[1,_1Hl,new T(function(){return B(A(_1HI,[_1HJ]));})]);});}:function(_1HK){return [1,_4d,new T(function(){return B(_1E(_1HF,[1,_1Hl,new T(function(){return B(A(_1HI,[[1,_4c,_1HK]]));})]));})];};},_1HL=E(_1HF);if(!_1HL[0]){return new F(function(){return _1HG(_);});}else{if(E(E(_1HL[1])[1])==40){var _1HM=E(_1HL[2]);if(!_1HM[0]){return new F(function(){return _1HG(_);});}else{if(E(E(_1HM[1])[1])==44){return function(_1HN){return [1,_1Hv,new T(function(){return B(A(new T(function(){return B(_1GI(_1Hu,_1HA));}),[[1,_1Hs,_1HN]]));})];};}else{return new F(function(){return _1HG(_);});}}}else{return new F(function(){return _1HG(_);});}}},_1HO=E(_1HA[2]);if(!_1HO[0]){var _1HP=E(_1Hy),_1HQ=E(_1Hc),_1HR=hs_eqWord64(_1HP[1],_1HQ[1]),_1HS=_1HR;if(!E(_1HS)){return new F(function(){return _1HD(_);});}else{var _1HT=hs_eqWord64(_1HP[2],_1HQ[2]),_1HU=_1HT;if(!E(_1HU)){return new F(function(){return _1HD(_);});}else{return function(_1HV){return [1,_1Hr,new T(function(){return B(A(new T(function(){var _1HW=E(_1HC);return B(_1GP(_1Hw,_1HW[3],_1HW[4]));}),[[1,_1Hq,_1HV]]));})];};}}}else{if(!E(_1HO[2])[0]){var _1HX=E(_1Hy),_1HY=E(_1GZ),_1HZ=hs_eqWord64(_1HX[1],_1HY[1]),_1I0=_1HZ;if(!E(_1I0)){return new F(function(){return _1HD(_);});}else{var _1I1=hs_eqWord64(_1HX[2],_1HY[2]),_1I2=_1I1;if(!E(_1I2)){return new F(function(){return _1HD(_);});}else{var _1I3=new T(function(){var _1I4=E(_1HO[1]);return B(_1GP(_1Hk,_1I4[3],_1I4[4]));}),_1I5=new T(function(){var _1I6=E(_1HC);return B(_1GP(_1Hp,_1I6[3],_1I6[4]));});return E(_1Hx)[1]<=8?function(_1I7){return new F(function(){return A(_1I5,[new T(function(){return B(_1E(_1Ho,new T(function(){return B(A(_1I3,[_1I7]));},1)));})]);});}:function(_1I8){return [1,_4d,new T(function(){return B(A(_1I5,[new T(function(){return B(_1E(_1Ho,new T(function(){return B(A(_1I3,[[1,_4c,_1I8]]));},1)));})]));})];};}}}else{return new F(function(){return _1HD(_);});}}}},_1I9=function(_1Ia,_1Ib){return new F(function(){return A(_1Ia,[function(_){return new F(function(){return jsFind(toJSStr(E(_1Ib)));});}]);});},_1Ic=[0],_1Id=function(_1Ie){return E(E(_1Ie)[3]);},_1If=new T(function(){return [0,"value"];}),_1Ig=function(_1Ih){return E(E(_1Ih)[6]);},_1Ii=function(_1Ij){return E(E(_1Ij)[1]);},_1Ik=new T(function(){return B(unCStr("Char"));}),_1Il=new T(function(){var _1Im=hs_wordToWord64(3763641161),_1In=_1Im,_1Io=hs_wordToWord64(1343745632),_1Ip=_1Io;return [0,_1In,_1Ip,[0,_1In,_1Ip,_1AC,_1H0,_1Ik],_f];}),_1Iq=function(_1Ir){return E(_1Il);},_1Is=function(_1It){return E(_1H2);},_1Iu=new T(function(){return B(_1BD(_1Is,_1Iq));}),_1Iv=new T(function(){return B(A(_1Iu,[_]));}),_1Iw=function(_1Ix,_1Iy,_1Iz,_1IA,_1IB,_1IC,_1ID,_1IE,_1IF){var _1IG=new T(function(){return B(A(_1IA,[_1Ic]));});return new F(function(){return A(_1Iy,[new T(function(){return B(_1I9(E(_1Ix)[2],_1IF));}),function(_1IH){var _1II=E(_1IH);return _1II[0]==0?E(_1IG):B(A(_1Iy,[new T(function(){return B(A(E(_1Ix)[2],[function(_){var _1IJ=jsGet(E(_1II[1])[1],E(_1If)[1]),_1IK=_1IJ;return [1,new T(function(){return fromJSStr(_1IK);})];}]));}),function(_1IL){var _1IM=E(_1IL);if(!_1IM[0]){return E(_1IG);}else{var _1IN=_1IM[1];if(!E(new T(function(){var _1IO=B(A(_1IC,[_])),_1IP=E(_1Iv),_1IQ=hs_eqWord64(_1IO[1],_1IP[1]),_1IR=_1IQ;if(!E(_1IR)){var _1IS=false;}else{var _1IT=hs_eqWord64(_1IO[2],_1IP[2]),_1IU=_1IT,_1IS=E(_1IU)==0?false:true;}var _1IV=_1IS,_1IW=_1IV;return _1IW;}))){var _1IX=function(_1IY){return new F(function(){return A(_1IA,[[1,_1IN,new T(function(){return B(A(new T(function(){return B(_1Ig(_1IE));}),[new T(function(){return B(A(new T(function(){return B(_1Id(_1IE));}),[new T(function(){return B(unAppCStr("can\'t read \"",new T(function(){return B(_1E(_1IN,new T(function(){return B(unAppCStr("\" as type ",new T(function(){var _1IZ=B(A(_1IC,[_]));return B(A(_1GP,[_1Hw,_1IZ[3],_1IZ[4],_f]));})));})));})));})]));})]));})]]);});},_1J0=B(A(new T(function(){return B(A(_1Ii,[_1ID,_I]));}),[_1IN]));if(!_1J0[0]){return new F(function(){return _1IX(_);});}else{var _1J1=E(_1J0[1]);return E(_1J1[2])[0]==0?E(_1J0[2])[0]==0?B(A(_1IA,[[2,_1J1[1]]])):B(_1IX(_)):B(_1IX(_));}}else{return new F(function(){return A(_1IA,[[2,_1IN]]);});}}}]));}]);});},_1J2=function(_1J3){return E(E(_1J3)[10]);},_1J4=function(_1J5){return new F(function(){return _Ed([1,function(_1J6){return new F(function(){return A(_LN,[_1J6,function(_1J7){return E(new T(function(){return B(_N3(function(_1J8){var _1J9=E(_1J8);return _1J9[0]==0?B(A(_1J5,[_1J9[1]])):[2];}));}));}]);});}],new T(function(){return [1,B(_Np(_1Ja,_1J5))];}));});},_1Ja=function(_1Jb,_1Jc){return new F(function(){return _1J4(_1Jc);});},_1Jd=[0,91],_1Je=[1,_1Jd,_f],_1Jf=function(_1Jg,_1Jh){var _1Ji=function(_1Jj,_1Jk){return [1,function(_1Jl){return new F(function(){return A(_LN,[_1Jl,function(_1Jm){return E(new T(function(){return B(_N3(function(_1Jn){var _1Jo=E(_1Jn);if(_1Jo[0]==2){var _1Jp=E(_1Jo[1]);if(!_1Jp[0]){return [2];}else{var _1Jq=_1Jp[2];switch(E(E(_1Jp[1])[1])){case 44:return E(_1Jq)[0]==0?!E(_1Jj)?[2]:E(new T(function(){return B(A(_1Jg,[_No,function(_1Jr){return new F(function(){return _1Ji(_Hk,function(_1Js){return new F(function(){return A(_1Jk,[[1,_1Jr,_1Js]]);});});});}]));})):[2];case 93:return E(_1Jq)[0]==0?E(new T(function(){return B(A(_1Jk,[_f]));})):[2];default:return [2];}}}else{return [2];}}));}));}]);});}];},_1Jt=function(_1Ju){return new F(function(){return _Ed([1,function(_1Jv){return new F(function(){return A(_LN,[_1Jv,function(_1Jw){return E(new T(function(){return B(_N3(function(_1Jx){var _1Jy=E(_1Jx);return _1Jy[0]==2?!B(_bv(_1Jy[1],_1Je))?[2]:E(new T(function(){return B(_Ed(B(_1Ji(_J,_1Ju)),new T(function(){return B(A(_1Jg,[_No,function(_1Jz){return new F(function(){return _1Ji(_Hk,function(_1JA){return new F(function(){return A(_1Ju,[[1,_1Jz,_1JA]]);});});});}]));})));})):[2];}));}));}]);});}],new T(function(){return [1,B(_Np(function(_1JB,_1JC){return new F(function(){return _1Jt(_1JC);});},_1Ju))];}));});};return new F(function(){return _1Jt(_1Jh);});},_1JD=function(_1JE){return new F(function(){return _Ed(B(_Ed([1,function(_1JF){return new F(function(){return A(_LN,[_1JF,function(_1JG){return E(new T(function(){return B(_N3(function(_1JH){var _1JI=E(_1JH);return _1JI[0]==1?B(A(_1JE,[_1JI[1]])):[2];}));}));}]);});}],new T(function(){return B(_1Jf(_1Ja,_1JE));}))),new T(function(){return [1,B(_Np(_1JJ,_1JE))];}));});},_1JJ=function(_1JK,_1JL){return new F(function(){return _1JD(_1JL);});},_1JM=new T(function(){return B(_1JD(_EW));}),_1JN=function(_1JO){return new F(function(){return _E3(_1JM,_1JO);});},_1JP=new T(function(){return B(_1J4(_EW));}),_1JQ=function(_1JO){return new F(function(){return _E3(_1JP,_1JO);});},_1JR=function(_1JS){return E(_1JQ);},_1JT=[0,_1JR,_1JN,_1Ja,_1JJ],_1JU=function(_1JV){return E(E(_1JV)[4]);},_1JW=function(_1JX,_1JY,_1JZ){return new F(function(){return _1Jf(new T(function(){return B(_1JU(_1JX));}),_1JZ);});},_1K0=function(_1K1){return function(_lZ){return new F(function(){return _E3(new T(function(){return B(_1Jf(new T(function(){return B(_1JU(_1K1));}),_EW));}),_lZ);});};},_1K2=function(_1K3,_1K4){return function(_lZ){return new F(function(){return _E3(new T(function(){return B(A(_1JU,[_1K3,_1K4,_EW]));}),_lZ);});};},_1K5=function(_1K6){return [0,function(_1JO){return new F(function(){return _1K2(_1K6,_1JO);});},new T(function(){return B(_1K0(_1K6));}),new T(function(){return B(_1JU(_1K6));}),function(_1K7,_1JO){return new F(function(){return _1JW(_1K6,_1K7,_1JO);});}];},_1K8=new T(function(){return B(_1K5(_1JT));}),_1K9=function(_1Ka,_1Kb,_1Kc){var _1Kd=new T(function(){return B(_1J2(_1Ka));}),_1Ke=new T(function(){return B(_1FY(_1Kc));}),_1Kf=new T(function(){return B(_BZ(_1Ke));});return function(_1Kg,_1Kh){return new F(function(){return A(new T(function(){return B(_17G(_1Ke));}),[new T(function(){return B(A(new T(function(){return B(_17G(_1Ke));}),[new T(function(){return B(A(new T(function(){return B(_BZ(_1Ke));}),[[0,_1Kh,_1Kh]]));}),function(_1Ki){var _1Kj=new T(function(){return E(E(_1Ki)[1]);}),_1Kk=new T(function(){return E(E(_1Kj)[2]);});return new F(function(){return A(new T(function(){return B(_17G(_1Ke));}),[new T(function(){return B(A(new T(function(){return B(_BZ(_1Ke));}),[[0,_0,new T(function(){var _1Kl=E(_1Kj);return [0,_1Kl[1],new T(function(){return [0,E(_1Kk)[1]+1|0];}),_1Kl[3],_1Kl[4],_1Kl[5],_1Kl[6],_1Kl[7]];})]]));}),function(_1Km){return new F(function(){return A(new T(function(){return B(_BZ(_1Ke));}),[[0,[1,_4k,new T(function(){return B(_1E(B(_4e(0,E(_1Kk)[1],_f)),new T(function(){return E(E(_1Kj)[1]);},1)));})],new T(function(){return E(E(_1Km)[2]);})]]);});}]);});}]));}),function(_1Kn){var _1Ko=new T(function(){return E(E(_1Kn)[1]);});return new F(function(){return A(new T(function(){return B(_17G(_1Ke));}),[new T(function(){return B(A(_1Iw,[new T(function(){return B(_1G8(new T(function(){return B(_1Gz(_1Ke));}),_1Kc));}),function(_1Kp,_1C7,_1Kq){return new F(function(){return _1Gc(_1Ke,_1Kp,_1C7,_1Kq);});},function(_1Kp,_1C7,_1Kq){return new F(function(){return _1Go(_1Ke,_1Kp,_1C7,_1Kq);});},function(_1C7,_1Kq){return new F(function(){return _1GD(_1Ke,_1C7,_1Kq);});},function(_1Kq){return new F(function(){return _1Gv(_1Ke,_1Kq);});},_1Iu,_1K8,_1Ka,_1Ko,new T(function(){return E(E(_1Kn)[2]);})]));}),function(_1Kr){var _1Ks=E(_1Kr),_1Kt=_1Ks[2],_1Ku=E(_1Ks[1]);switch(_1Ku[0]){case 0:return new F(function(){return A(_1Kf,[[0,[0,new T(function(){return B(A(_1Kd,[_1Ko,_1Kg]));}),_Z],_1Kt]]);});break;case 1:return new F(function(){return A(_1Kf,[[0,[0,new T(function(){return B(A(_1Kd,[_1Ko,_1Ku[1]]));}),_Z],_1Kt]]);});break;default:var _1Kv=_1Ku[1];return new F(function(){return A(_1Kf,[[0,[0,new T(function(){return B(A(_1Kd,[_1Ko,_1Kv]));}),[1,_1Kv]],_1Kt]]);});}}]);});}]);});};},_1Kw=new T(function(){return B(_1K9(_1Ee,_1Ep,_1FX));}),_1Kx=function(_1Ky){return E(E(_1Ky)[2]);},_1Kz=function(_1KA){return E(E(_1KA)[1]);},_1KB=function(_1KC,_1KD,_1KE){return function(_1KF,_){var _1KG=B(A(_1KD,[_1KF,_])),_1KH=_1KG,_1KI=E(_1KH),_1KJ=E(_1KI[1]),_1KK=new T(function(){return B(A(new T(function(){return B(_1Kx(_1KC));}),[_1KE,function(_){var _1KL=E(E(_1KF)[4]),_1KM=B(A(_1KL[1],[_])),_1KN=_1KM,_1KO=E(_1KN);if(!_1KO[0]){return _0;}else{var _1KP=B(A(_1KL[2],[_1KO[1],_])),_1KQ=_1KP;return _0;}}]));});return [0,[0,function(_1KR,_){var _1KS=B(A(_1KJ[1],[_1KR,_])),_1KT=_1KS,_1KU=E(_1KT),_1KV=E(_1KK),_1KW=jsSetCB(_1KU[1],toJSStr(E(new T(function(){return B(A(_1Kz,[_1KC,_1KE]));}))),_1KK),_1KX=_1KW;return _1KU;},_1KJ[2]],_1KI[2]];};},_1KY=function(_1KZ){return function(_lZ,_m0){return new F(function(){return _56(function(_1L0,_){var _1L1=B(A(new T(function(){return B(_1KB(_40,new T(function(){return B(A(_1Kw,[_1KZ]));}),_g));}),[_1L0,_])),_1L2=_1L1,_1L3=E(_1L2),_1L4=E(_1L3[1]);return [0,[0,function(_1L5,_){var _1L6=B(A(_1L4[1],[_1L5,_])),_1L7=_1L6,_1L8=B(A(_41,[_4r,_1L7,_1yw,_1Al,_])),_1L9=_1L8;return _1L7;},_1L4[2]],_1L3[2]];},_1zP,_lZ,_m0);});};},_1La=new T(function(){return B(unCStr("innerHTML"));}),_1Lb=function(_1Lc,_){var _1Ld=B(_4(_1Lc,_1La,_)),_1Le=_1Ld,_1Lf=[0,_1Lc],_1Lg=B(A(_9,[_4r,_1Lf,_1La,_f,_])),_1Lh=_1Lg,_1Li=E(_1c)[1],_1Lj=takeMVar(_1Li),_1Lk=_1Lj,_1Ll=B(A(_1KY,[_1Le,_1Lk,_])),_1Lm=_1Ll,_1Ln=E(_1Lm),_1Lo=E(_1Ln[1]),_=putMVar(_1Li,_1Ln[2]),_1Lp=B(A(_1Lo[1],[_1Lf,_])),_1Lq=_1Lp;return _1Lo[2];},_1Lr=function(_1Ls,_){while(1){var _1Lt=E(_1Ls);if(!_1Lt[0]){return _0;}else{var _1Lu=B(_1Lb(E(_1Lt[1])[1],_)),_1Lv=_1Lu;_1Ls=_1Lt[2];continue;}}},_1Lw=function(_){var _1Lx=jsElemsByClassName("proofbox"),_1Ly=_1Lx,_1Lz=B(_1Lr(_1Ly,_)),_1LA=_1Lz,_1LB=jsSetTimeout(60,_1);return _0;},_1LC=function(_){return new F(function(){return _1Lw(_);});};
var hasteMain = function() {B(A(_1LC, [0]));};window.onload = hasteMain;