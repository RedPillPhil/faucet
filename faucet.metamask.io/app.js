// LavaMoat Prelude
(function() {

  // identify the globalRef
  const globalRef = (typeof globalThis !== 'undefined') ? globalThis : (typeof self !== 'undefined') ? self : (typeof global !== 'undefined') ? global : undefined
  if (!globalRef) {
    throw new Error('Lavamoat - unable to identify globalRef')
  }

  // config and bundle module store
  const lavamoatConfig = { resources: {} }
  const modules = {}

  // initialize the kernel
  const createKernel = // LavaMoat Prelude
(function () {
  return createKernel

  function createKernel ({
    lavamoatConfig,
    loadModuleData,
    getRelativeModuleId,
    prepareModuleInitializerArgs,
    getExternalCompartment,
    globalThisRefs,
  }) {
    const debugMode = false

    // identify the globalRef
    const globalRef = (typeof globalThis !== 'undefined') ? globalThis : (typeof self !== 'undefined') ? self : (typeof global !== 'undefined') ? global : undefined
    if (!globalRef) {
      throw new Error('Lavamoat - unable to identify globalRef')
    }

    // polyfill globalThis
    if (globalRef && !globalRef.globalThis) {
      globalRef.globalThis = globalRef
    }

    // create the SES rootRealm
    // "templateRequire" calls are inlined in "generatePrelude"
    // load-bearing semi-colon, do not remove
    ;// define ses
(function(){
  const global = globalRef
  const exports = {}
  const module = { exports }
  ;(function(){
// START of injected code from ses
(function (factory) {
  typeof define === 'function' && define.amd ? define(factory) :
  factory();
}((function () { 'use strict';

  /**
   * commons.js
   * Declare shorthand functions. Sharing these declarations across modules
   * improves on consistency and minification. Unused declarations are
   * dropped by the tree shaking process.
   *
   * We capture these, not just for brevity, but for security. If any code
   * modifies Object to change what 'assign' points to, the Compartment shim
   * would be corrupted.
   */

  const {
    assign,
    create,
    defineProperties,
    entries,
    freeze,
    getOwnPropertyDescriptor,
    getOwnPropertyDescriptors,
    getOwnPropertyNames,
    getPrototypeOf,
    is,
    isExtensible,
    keys,
    prototype: objectPrototype,
    seal,
    setPrototypeOf,
    values,
  } = Object;

  // At time of this writing, we still support Node 10 which doesn't have
  // `Object.fromEntries`. If it is absent, this should be an adequate
  // replacement.
  // By the terminology of https://ponyfoo.com/articles/polyfills-or-ponyfills
  // it is a ponyfill rather than a polyfill or shim because we do not
  // install it on `Object`.
  const objectFromEntries = entryPairs => {
    const result = {};
    for (const [prop, val] of entryPairs) {
      result[prop] = val;
    }
    return result;
  };

  const fromEntries = Object.fromEntries || objectFromEntries;

  const defineProperty = (object, prop, descriptor) => {
    // Object.defineProperty is allowed to fail silently so we use
    // Object.defineProperties instead.
    return defineProperties(object, { [prop]: descriptor });
  };

  const { apply, construct, get: reflectGet, set: reflectSet } = Reflect;

  const { isArray, prototype: arrayPrototype } = Array;
  const { revocable: proxyRevocable } = Proxy;
  const { prototype: regexpPrototype } = RegExp;
  const { prototype: stringPrototype } = String;
  const { prototype: weakmapPrototype } = WeakMap;

  /**
   * uncurryThis()
   * This form of uncurry uses Reflect.apply()
   *
   * The original uncurry uses:
   * const bind = Function.prototype.bind;
   * const uncurryThis = bind.bind(bind.call);
   *
   * See those reference for a complete explanation:
   * http://wiki.ecmascript.org/doku.php?id=conventions:safe_meta_programming
   * which only lives at
   * http://web.archive.org/web/20160805225710/http://wiki.ecmascript.org/doku.php?id=conventions:safe_meta_programming
   *
   * @param {(thisArg: Object, ...args: any[]) => any} fn
   */
  const uncurryThis = fn => (thisArg, ...args) => apply(fn, thisArg, args);

  const objectHasOwnProperty = uncurryThis(objectPrototype.hasOwnProperty);
  //
  const arrayFilter = uncurryThis(arrayPrototype.filter);
  const arrayJoin = uncurryThis(arrayPrototype.join);
  const arrayPush = uncurryThis(arrayPrototype.push);
  const arrayPop = uncurryThis(arrayPrototype.pop);
  const arrayIncludes = uncurryThis(arrayPrototype.includes);
  //
  const regexpTest = uncurryThis(regexpPrototype.test);
  //
  const stringMatch = uncurryThis(stringPrototype.match);
  const stringSearch = uncurryThis(stringPrototype.search);
  const stringSlice = uncurryThis(stringPrototype.slice);
  const stringSplit = uncurryThis(stringPrototype.split);
  //
  const weakmapGet = uncurryThis(weakmapPrototype.get);
  const weakmapSet = uncurryThis(weakmapPrototype.set);
  const weakmapHas = uncurryThis(weakmapPrototype.has);

  /**
   * immutableObject
   * An immutable (frozen) exotic object and is safe to share.
   */
  const immutableObject = freeze({ __proto__: null });

  const nativeSuffix = ') { [native code] }';

  // Note: Top level mutable state. Does not make anything worse, since the
  // patching of `Function.prototype.toString` is also globally stateful. We
  // use this top level state so that multiple calls to `tameFunctionToString` are
  // idempotent, rather than creating redundant indirections.
  let nativeBrander;

  /**
   * Replace `Function.prototype.toString` with one that recognizes
   * shimmed functions as honorary native functions.
   */
  function tameFunctionToString() {
    if (nativeBrander === undefined) {
      const nativeBrand = new WeakSet();

      const originalFunctionToString = Function.prototype.toString;

      const tamingMethods = {
        toString() {
          const str = apply(originalFunctionToString, this, []);
          if (str.endsWith(nativeSuffix) || !nativeBrand.has(this)) {
            return str;
          }
          return `function ${this.name}() { [native code] }`;
        },
      };

      defineProperty(Function.prototype, 'toString', {
        value: tamingMethods.toString,
      });

      nativeBrander = freeze(func => nativeBrand.add(func));
    }
    return nativeBrander;
  }

  /**
   * @file Exports {@code whitelist}, a recursively defined
   * JSON record enumerating all intrinsics and their properties
   * according to ECMA specs.
   *
   * @author JF Paradis
   * @author Mark S. Miller
   */

  /* eslint max-lines: 0 */

  /**
   * constantProperties
   * non-configurable, non-writable data properties of all global objects.
   * Must be powerless.
   * Maps from property name to the actual value
   */
  const constantProperties = {
    // *** Value Properties of the Global Object

    Infinity,
    NaN,
    undefined,
  };

  /**
   * universalPropertyNames
   * Properties of all global objects.
   * Must be powerless.
   * Maps from property name to the intrinsic name in the whitelist.
   */
  const universalPropertyNames = {
    // *** Function Properties of the Global Object

    isFinite: 'isFinite',
    isNaN: 'isNaN',
    parseFloat: 'parseFloat',
    parseInt: 'parseInt',

    decodeURI: 'decodeURI',
    decodeURIComponent: 'decodeURIComponent',
    encodeURI: 'encodeURI',
    encodeURIComponent: 'encodeURIComponent',

    // *** Constructor Properties of the Global Object

    Array: 'Array',
    ArrayBuffer: 'ArrayBuffer',
    BigInt: 'BigInt',
    BigInt64Array: 'BigInt64Array',
    BigUint64Array: 'BigUint64Array',
    Boolean: 'Boolean',
    DataView: 'DataView',
    EvalError: 'EvalError',
    Float32Array: 'Float32Array',
    Float64Array: 'Float64Array',
    Int8Array: 'Int8Array',
    Int16Array: 'Int16Array',
    Int32Array: 'Int32Array',
    Map: 'Map',
    Number: 'Number',
    Object: 'Object',
    Promise: 'Promise',
    Proxy: 'Proxy',
    RangeError: 'RangeError',
    ReferenceError: 'ReferenceError',
    Set: 'Set',
    String: 'String',
    Symbol: 'Symbol',
    SyntaxError: 'SyntaxError',
    TypeError: 'TypeError',
    Uint8Array: 'Uint8Array',
    Uint8ClampedArray: 'Uint8ClampedArray',
    Uint16Array: 'Uint16Array',
    Uint32Array: 'Uint32Array',
    URIError: 'URIError',
    WeakMap: 'WeakMap',
    WeakSet: 'WeakSet',

    // *** Other Properties of the Global Object

    JSON: 'JSON',
    Reflect: 'Reflect',

    // *** Annex B

    escape: 'escape',
    unescape: 'unescape',

    // ESNext

    lockdown: 'lockdown',
    harden: 'harden',
    HandledPromise: 'HandledPromise', // TODO: Until Promise.delegate (see below).
    StaticModuleRecord: 'StaticModuleRecord',
  };

  /**
   * initialGlobalPropertyNames
   * Those found only on the initial global, i.e., the global of the
   * start compartment, as well as any compartments created before lockdown.
   * These may provide much of the power provided by the original.
   * Maps from property name to the intrinsic name in the whitelist.
   */
  const initialGlobalPropertyNames = {
    // *** Constructor Properties of the Global Object

    Date: '%InitialDate%',
    Error: '%InitialError%',
    RegExp: '%InitialRegExp%',

    // *** Other Properties of the Global Object

    Math: '%InitialMath%',

    // ESNext

    // From Error-stack proposal
    // Only on initial global. No corresponding
    // powerless form for other globals.
    getStackString: '%InitialGetStackString%',

    // TODO https://github.com/Agoric/SES-shim/issues/551
    // Need initial WeakRef and FinalizationGroup in
    // start compartment only.
  };

  /**
   * sharedGlobalPropertyNames
   * Those found only on the globals of new compartments created after lockdown,
   * which must therefore be powerless.
   * Maps from property name to the intrinsic name in the whitelist.
   */
  const sharedGlobalPropertyNames = {
    // *** Constructor Properties of the Global Object

    Date: '%SharedDate%',
    Error: '%SharedError%',
    RegExp: '%SharedRegExp%',

    // *** Other Properties of the Global Object

    Math: '%SharedMath%',
  };

  // All the "subclasses" of Error. These are collectively represented in the
  // EcmaScript spec by the meta variable NativeError.
  // TODO Add AggregateError https://github.com/Agoric/SES-shim/issues/550
  const NativeErrors = [
    EvalError,
    RangeError,
    ReferenceError,
    SyntaxError,
    TypeError,
    URIError,
  ];

  /**
   * <p>Each JSON record enumerates the disposition of the properties on
   *    some corresponding intrinsic object.
   *
   * <p>All records are made of key-value pairs where the key
   *    is the property to process, and the value is the associated
   *    dispositions a.k.a. the "permit". Those permits can be:
   * <ul>
   * <li>The boolean value "false", in which case this property is
   *     blacklisted and simply removed. Properties not mentioned
   *     are also considered blacklisted and are removed.
   * <li>A string value equal to a primitive ("number", "string", etc),
   *     in which case the property is whitelisted if its value property
   *     is typeof the given type. For example, {@code "Infinity"} leads to
   *     "number" and property values that fail {@code typeof "number"}.
   *     are removed.
   * <li>A string value equal to an intinsic name ("ObjectPrototype",
   *     "Array", etc), in which case the property whitelisted if its
   *     value property is equal to the value of the corresponfing
   *     intrinsics. For example, {@code Map.prototype} leads to
   *     "MapPrototype" and the property is removed if its value is
   *     not equal to %MapPrototype%
   * <li>Another record, in which case this property is simply
   *     whitelisted and that next record represents the disposition of
   *     the object which is its value. For example, {@code "Object"}
   *     leads to another record explaining what properties {@code
   *     "Object"} may have and how each such property should be treated.
   *
   * <p>Notes:
   * <li>"[[Proto]]" is used to refer to the "[[Prototype]]" internal
   *     slot, which says which object this object inherits from.
   * <li>"--proto--" is used to refer to the "__proto__" property name,
   *     which is the name of an accessor property on Object.prototype.
   *     In practice, it is used to access the [[Proto]] internal slot,
   *     but is distinct from the internal slot itself. We use
   *     "--proto--" rather than "__proto__" below because "__proto__"
   *     in an object literal is special syntax rather than a normal
   *     property definition.
   * <li>"ObjectPrototype" is the default "[[Proto]]" (when not specified).
   * <li>Constants "fn" and "getter" are used to keep the structure DRY.
   * <li>Symbol properties are listed using the "@@name" form.
   */

  // Function Instances
  const FunctionInstance = {
    '[[Proto]]': '%FunctionPrototype%',
    length: 'number',
    name: 'string',
    // Do not specify "prototype" here, since only Function instances that can
    // be used as a constructor have a prototype property. For constructors,
    // since prototype properties are instance-specific, we define it there.
  };

  // Aliases
  const fn = FunctionInstance;

  const getter = {
    get: fn,
    set: 'undefined',
  };

  // Possible but not encountered in the specs
  // export const setter = {
  //   get: 'undefined',
  //   set: fn,
  // };

  const accessor = {
    get: fn,
    set: fn,
  };

  function isAccessorPermit(permit) {
    return permit === getter || permit === accessor;
  }

  // NativeError Object Structure
  function NativeError(prototype) {
    return {
      // Properties of the NativeError Constructors
      '[[Proto]]': '%SharedError%',

      // NativeError.prototype
      prototype,
    };
  }

  function NativeErrorPrototype(constructor) {
    return {
      // Properties of the NativeError Prototype Objects
      '[[Proto]]': '%ErrorPrototype%',
      constructor,
      message: 'string',
      name: 'string',
      // Redundantly present only on v8. Safe to remove.
      toString: false,
    };
  }

  // The TypedArray Constructors
  function TypedArray(prototype) {
    return {
      // Properties of the TypedArray Constructors
      '[[Proto]]': '%TypedArray%',
      BYTES_PER_ELEMENT: 'number',
      prototype,
    };
  }

  function TypedArrayPrototype(constructor) {
    return {
      // Properties of the TypedArray Prototype Objects
      '[[Proto]]': '%TypedArrayPrototype%',
      BYTES_PER_ELEMENT: 'number',
      constructor,
    };
  }

  // Without Math.random
  const SharedMath = {
    E: 'number',
    LN10: 'number',
    LN2: 'number',
    LOG10E: 'number',
    LOG2E: 'number',
    PI: 'number',
    SQRT1_2: 'number',
    SQRT2: 'number',
    '@@toStringTag': 'string',
    abs: fn,
    acos: fn,
    acosh: fn,
    asin: fn,
    asinh: fn,
    atan: fn,
    atanh: fn,
    atan2: fn,
    cbrt: fn,
    ceil: fn,
    clz32: fn,
    cos: fn,
    cosh: fn,
    exp: fn,
    expm1: fn,
    floor: fn,
    fround: fn,
    hypot: fn,
    imul: fn,
    log: fn,
    log1p: fn,
    log10: fn,
    log2: fn,
    max: fn,
    min: fn,
    pow: fn,
    round: fn,
    sign: fn,
    sin: fn,
    sinh: fn,
    sqrt: fn,
    tan: fn,
    tanh: fn,
    trunc: fn,
    // See https://github.com/Moddable-OpenSource/moddable/issues/523
    idiv: false,
    // See https://github.com/Moddable-OpenSource/moddable/issues/523
    idivmod: false,
    // See https://github.com/Moddable-OpenSource/moddable/issues/523
    imod: false,
    // See https://github.com/Moddable-OpenSource/moddable/issues/523
    imuldiv: false,
    // See https://github.com/Moddable-OpenSource/moddable/issues/523
    irem: false,
    // See https://github.com/Moddable-OpenSource/moddable/issues/523
    mod: false,
  };

  const whitelist = {
    // ECMA https://tc39.es/ecma262

    // The intrinsics object has no prototype to avoid conflicts.
    '[[Proto]]': null,

    // %ThrowTypeError%
    '%ThrowTypeError%': fn,

    // *** The Global Object

    // *** Value Properties of the Global Object
    Infinity: 'number',
    NaN: 'number',
    undefined: 'undefined',

    // *** Function Properties of the Global Object

    // eval
    '%UniqueEval%': fn,
    isFinite: fn,
    isNaN: fn,
    parseFloat: fn,
    parseInt: fn,
    decodeURI: fn,
    decodeURIComponent: fn,
    encodeURI: fn,
    encodeURIComponent: fn,

    // *** Fundamental Objects

    Object: {
      // Properties of the Object Constructor
      '[[Proto]]': '%FunctionPrototype%',
      assign: fn,
      create: fn,
      defineProperties: fn,
      defineProperty: fn,
      entries: fn,
      freeze: fn,
      fromEntries: fn,
      getOwnPropertyDescriptor: fn,
      getOwnPropertyDescriptors: fn,
      getOwnPropertyNames: fn,
      getOwnPropertySymbols: fn,
      getPrototypeOf: fn,
      is: fn,
      isExtensible: fn,
      isFrozen: fn,
      isSealed: fn,
      keys: fn,
      preventExtensions: fn,
      prototype: '%ObjectPrototype%',
      seal: fn,
      setPrototypeOf: fn,
      values: fn,
    },

    '%ObjectPrototype%': {
      // Properties of the Object Prototype Object
      '[[Proto]]': null,
      constructor: 'Object',
      hasOwnProperty: fn,
      isPrototypeOf: fn,
      propertyIsEnumerable: fn,
      toLocaleString: fn,
      toString: fn,
      valueOf: fn,

      // Annex B: Additional Properties of the Object.prototype Object

      '--proto--': accessor,
      __defineGetter__: fn,
      __defineSetter__: fn,
      __lookupGetter__: fn,
      __lookupSetter__: fn,
    },

    '%UniqueFunction%': {
      // Properties of the Function Constructor
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%FunctionPrototype%',
    },

    '%InertFunction%': {
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%FunctionPrototype%',
    },

    '%FunctionPrototype%': {
      apply: fn,
      bind: fn,
      call: fn,
      constructor: '%InertFunction%', // TODO test
      toString: fn,
      '@@hasInstance': fn,
      // proposed but not yet std yet. To be removed if there
      caller: false,
      // proposed but not yet std yet. To be removed if there
      arguments: false,
    },

    Boolean: {
      // Properties of the Boolean Constructor
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%BooleanPrototype%',
    },

    '%BooleanPrototype%': {
      constructor: 'Boolean',
      toString: fn,
      valueOf: fn,
    },

    Symbol: {
      // Properties of the Symbol Constructor
      '[[Proto]]': '%FunctionPrototype%',
      asyncIterator: 'symbol',
      for: fn,
      hasInstance: 'symbol',
      isConcatSpreadable: 'symbol',
      iterator: 'symbol',
      keyFor: fn,
      match: 'symbol',
      matchAll: 'symbol',
      prototype: '%SymbolPrototype%',
      replace: 'symbol',
      search: 'symbol',
      species: 'symbol',
      split: 'symbol',
      toPrimitive: 'symbol',
      toStringTag: 'symbol',
      unscopables: 'symbol',
    },

    '%SymbolPrototype%': {
      // Properties of the Symbol Prototype Object
      constructor: 'Symbol',
      description: getter,
      toString: fn,
      valueOf: fn,
      '@@toPrimitive': fn,
      '@@toStringTag': 'string',
    },

    '%InitialError%': {
      // Properties of the Error Constructor
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%ErrorPrototype%',
      // Non standard, v8 only, used by tap
      captureStackTrace: fn,
      // Non standard, v8 only, used by tap, tamed to accessor
      stackTraceLimit: accessor,
      // Non standard, v8 only, used by several, tamed to accessor
      prepareStackTrace: accessor,
    },

    '%SharedError%': {
      // Properties of the Error Constructor
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%ErrorPrototype%',
      // Non standard, v8 only, used by tap
      captureStackTrace: fn,
      // Non standard, v8 only, used by tap, tamed to accessor
      stackTraceLimit: accessor,
      // Non standard, v8 only, used by several, tamed to accessor
      prepareStackTrace: accessor,
    },

    '%ErrorPrototype%': {
      constructor: '%SharedError%',
      message: 'string',
      name: 'string',
      toString: fn,
      // proposed de-facto, assumed TODO
      // Seen on FF Nightly 88.0a1
      at: false,
      // Seen on FF and XS
      stack: false,
    },

    // NativeError

    EvalError: NativeError('%EvalErrorPrototype%'),
    RangeError: NativeError('%RangeErrorPrototype%'),
    ReferenceError: NativeError('%ReferenceErrorPrototype%'),
    SyntaxError: NativeError('%SyntaxErrorPrototype%'),
    TypeError: NativeError('%TypeErrorPrototype%'),
    URIError: NativeError('%URIErrorPrototype%'),

    '%EvalErrorPrototype%': NativeErrorPrototype('EvalError'),
    '%RangeErrorPrototype%': NativeErrorPrototype('RangeError'),
    '%ReferenceErrorPrototype%': NativeErrorPrototype('ReferenceError'),
    '%SyntaxErrorPrototype%': NativeErrorPrototype('SyntaxError'),
    '%TypeErrorPrototype%': NativeErrorPrototype('TypeError'),
    '%URIErrorPrototype%': NativeErrorPrototype('URIError'),

    // *** Numbers and Dates

    Number: {
      // Properties of the Number Constructor
      '[[Proto]]': '%FunctionPrototype%',
      EPSILON: 'number',
      isFinite: fn,
      isInteger: fn,
      isNaN: fn,
      isSafeInteger: fn,
      MAX_SAFE_INTEGER: 'number',
      MAX_VALUE: 'number',
      MIN_SAFE_INTEGER: 'number',
      MIN_VALUE: 'number',
      NaN: 'number',
      NEGATIVE_INFINITY: 'number',
      parseFloat: fn,
      parseInt: fn,
      POSITIVE_INFINITY: 'number',
      prototype: '%NumberPrototype%',
    },

    '%NumberPrototype%': {
      // Properties of the Number Prototype Object
      constructor: 'Number',
      toExponential: fn,
      toFixed: fn,
      toLocaleString: fn,
      toPrecision: fn,
      toString: fn,
      valueOf: fn,
    },

    BigInt: {
      // Properties of the BigInt Constructor
      '[[Proto]]': '%FunctionPrototype%',
      asIntN: fn,
      asUintN: fn,
      prototype: '%BigIntPrototype%',
      // See https://github.com/Moddable-OpenSource/moddable/issues/523
      bitLength: false,
      // See https://github.com/Moddable-OpenSource/moddable/issues/523
      fromArrayBuffer: false,
    },

    '%BigIntPrototype%': {
      constructor: 'BigInt',
      toLocaleString: fn,
      toString: fn,
      valueOf: fn,
      '@@toStringTag': 'string',
    },

    '%InitialMath%': {
      ...SharedMath,
      // random is standard but omitted from SharedMath
      random: fn,
    },

    '%SharedMath%': SharedMath,

    '%InitialDate%': {
      // Properties of the Date Constructor
      '[[Proto]]': '%FunctionPrototype%',
      now: fn,
      parse: fn,
      prototype: '%DatePrototype%',
      UTC: fn,
    },

    '%SharedDate%': {
      // Properties of the Date Constructor
      '[[Proto]]': '%FunctionPrototype%',
      now: fn,
      parse: fn,
      prototype: '%DatePrototype%',
      UTC: fn,
    },

    '%DatePrototype%': {
      constructor: '%SharedDate%',
      getDate: fn,
      getDay: fn,
      getFullYear: fn,
      getHours: fn,
      getMilliseconds: fn,
      getMinutes: fn,
      getMonth: fn,
      getSeconds: fn,
      getTime: fn,
      getTimezoneOffset: fn,
      getUTCDate: fn,
      getUTCDay: fn,
      getUTCFullYear: fn,
      getUTCHours: fn,
      getUTCMilliseconds: fn,
      getUTCMinutes: fn,
      getUTCMonth: fn,
      getUTCSeconds: fn,
      setDate: fn,
      setFullYear: fn,
      setHours: fn,
      setMilliseconds: fn,
      setMinutes: fn,
      setMonth: fn,
      setSeconds: fn,
      setTime: fn,
      setUTCDate: fn,
      setUTCFullYear: fn,
      setUTCHours: fn,
      setUTCMilliseconds: fn,
      setUTCMinutes: fn,
      setUTCMonth: fn,
      setUTCSeconds: fn,
      toDateString: fn,
      toISOString: fn,
      toJSON: fn,
      toLocaleDateString: fn,
      toLocaleString: fn,
      toLocaleTimeString: fn,
      toString: fn,
      toTimeString: fn,
      toUTCString: fn,
      valueOf: fn,
      '@@toPrimitive': fn,

      // Annex B: Additional Properties of the Date.prototype Object
      getYear: fn,
      setYear: fn,
      toGMTString: fn,
    },

    // Text Processing

    String: {
      // Properties of the String Constructor
      '[[Proto]]': '%FunctionPrototype%',
      fromCharCode: fn,
      fromCodePoint: fn,
      prototype: '%StringPrototype%',
      raw: fn,
      // See https://github.com/Moddable-OpenSource/moddable/issues/523
      fromArrayBuffer: false,
    },

    '%StringPrototype%': {
      // Properties of the String Prototype Object
      length: 'number',
      charAt: fn,
      charCodeAt: fn,
      codePointAt: fn,
      concat: fn,
      constructor: 'String',
      endsWith: fn,
      includes: fn,
      indexOf: fn,
      lastIndexOf: fn,
      localeCompare: fn,
      match: fn,
      matchAll: fn,
      normalize: fn,
      padEnd: fn,
      padStart: fn,
      repeat: fn,
      replace: fn,
      replaceAll: fn, // ES2021
      search: fn,
      slice: fn,
      split: fn,
      startsWith: fn,
      substring: fn,
      toLocaleLowerCase: fn,
      toLocaleUpperCase: fn,
      toLowerCase: fn,
      toString: fn,
      toUpperCase: fn,
      trim: fn,
      trimEnd: fn,
      trimStart: fn,
      valueOf: fn,
      '@@iterator': fn,

      // Annex B: Additional Properties of the String.prototype Object
      substr: fn,
      anchor: fn,
      big: fn,
      blink: fn,
      bold: fn,
      fixed: fn,
      fontcolor: fn,
      fontsize: fn,
      italics: fn,
      link: fn,
      small: fn,
      strike: fn,
      sub: fn,
      sup: fn,
      trimLeft: fn,
      trimRight: fn,
      // See https://github.com/Moddable-OpenSource/moddable/issues/523
      compare: false,
    },

    '%StringIteratorPrototype%': {
      '[[Proto]]': '%IteratorPrototype%',
      next: fn,
      '@@toStringTag': 'string',
    },

    '%InitialRegExp%': {
      // Properties of the RegExp Constructor
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%RegExpPrototype%',
      '@@species': getter,

      // The https://github.com/tc39/proposal-regexp-legacy-features
      // are all optional, unsafe, and omitted
      input: false,
      $_: false,
      lastMatch: false,
      '$&': false,
      lastParen: false,
      '$+': false,
      leftContext: false,
      '$`': false,
      rightContext: false,
      "$'": false,
      $1: false,
      $2: false,
      $3: false,
      $4: false,
      $5: false,
      $6: false,
      $7: false,
      $8: false,
      $9: false,
    },

    '%SharedRegExp%': {
      // Properties of the RegExp Constructor
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%RegExpPrototype%',
      '@@species': getter,
    },

    '%RegExpPrototype%': {
      // Properties of the RegExp Prototype Object
      constructor: '%SharedRegExp%',
      exec: fn,
      dotAll: getter,
      flags: getter,
      global: getter,
      ignoreCase: getter,
      '@@match': fn,
      '@@matchAll': fn,
      multiline: getter,
      '@@replace': fn,
      '@@search': fn,
      source: getter,
      '@@split': fn,
      sticky: getter,
      test: fn,
      toString: fn,
      unicode: getter,

      // Annex B: Additional Properties of the RegExp.prototype Object
      compile: false, // UNSAFE and suppressed.
      // Seen on FF Nightly 88.0a1, Chrome Canary 91.0.4446.0,
      // Safari Tech Preview Release 122 (Safari 14.2, WebKit 16612.1.6.2)
      hasIndices: false,
    },

    '%RegExpStringIteratorPrototype%': {
      // The %RegExpStringIteratorPrototype% Object
      '[[Proto]]': '%IteratorPrototype%',
      next: fn,
      '@@toStringTag': 'string',
    },

    // Indexed Collections

    Array: {
      // Properties of the Array Constructor
      '[[Proto]]': '%FunctionPrototype%',
      from: fn,
      isArray: fn,
      of: fn,
      prototype: '%ArrayPrototype%',
      '@@species': getter,
    },

    '%ArrayPrototype%': {
      // Properties of the Array Prototype Object
      length: 'number',
      concat: fn,
      constructor: 'Array',
      copyWithin: fn,
      entries: fn,
      every: fn,
      fill: fn,
      filter: fn,
      find: fn,
      findIndex: fn,
      flat: fn,
      flatMap: fn,
      forEach: fn,
      includes: fn,
      indexOf: fn,
      join: fn,
      keys: fn,
      lastIndexOf: fn,
      map: fn,
      pop: fn,
      push: fn,
      reduce: fn,
      reduceRight: fn,
      reverse: fn,
      shift: fn,
      slice: fn,
      some: fn,
      sort: fn,
      splice: fn,
      toLocaleString: fn,
      toString: fn,
      unshift: fn,
      values: fn,
      '@@iterator': fn,
      '@@unscopables': {
        '[[Proto]]': null,
        copyWithin: 'boolean',
        entries: 'boolean',
        fill: 'boolean',
        find: 'boolean',
        findIndex: 'boolean',
        flat: 'boolean',
        flatMap: 'boolean',
        includes: 'boolean',
        keys: 'boolean',
        values: 'boolean',
        // Failed tc39 proposal
        // Seen on FF Nightly 88.0a1
        at: false,
      },
      // Failed tc39 proposal
      // Seen on FF Nightly 88.0a1
      at: false,
    },

    '%ArrayIteratorPrototype%': {
      // The %ArrayIteratorPrototype% Object
      '[[Proto]]': '%IteratorPrototype%',
      next: fn,
      '@@toStringTag': 'string',
    },

    // *** TypedArray Objects

    '%TypedArray%': {
      // Properties of the %TypedArray% Intrinsic Object
      '[[Proto]]': '%FunctionPrototype%',
      from: fn,
      of: fn,
      prototype: '%TypedArrayPrototype%',
      '@@species': getter,
    },

    '%TypedArrayPrototype%': {
      buffer: getter,
      byteLength: getter,
      byteOffset: getter,
      constructor: '%TypedArray%',
      copyWithin: fn,
      entries: fn,
      every: fn,
      fill: fn,
      filter: fn,
      find: fn,
      findIndex: fn,
      forEach: fn,
      includes: fn,
      indexOf: fn,
      join: fn,
      keys: fn,
      lastIndexOf: fn,
      length: getter,
      map: fn,
      reduce: fn,
      reduceRight: fn,
      reverse: fn,
      set: fn,
      slice: fn,
      some: fn,
      sort: fn,
      subarray: fn,
      toLocaleString: fn,
      toString: fn,
      values: fn,
      '@@iterator': fn,
      '@@toStringTag': getter,
      // Failed tc39 proposal
      // Seen on FF Nightly 88.0a1
      at: false,
    },

    // The TypedArray Constructors

    BigInt64Array: TypedArray('%BigInt64ArrayPrototype%'),
    BigUint64Array: TypedArray('%BigUint64ArrayPrototype%'),
    Float32Array: TypedArray('%Float32ArrayPrototype%'),
    Float64Array: TypedArray('%Float64ArrayPrototype%'),
    Int16Array: TypedArray('%Int16ArrayPrototype%'),
    Int32Array: TypedArray('%Int32ArrayPrototype%'),
    Int8Array: TypedArray('%Int8ArrayPrototype%'),
    Uint16Array: TypedArray('%Uint16ArrayPrototype%'),
    Uint32Array: TypedArray('%Uint32ArrayPrototype%'),
    Uint8Array: TypedArray('%Uint8ArrayPrototype%'),
    Uint8ClampedArray: TypedArray('%Uint8ClampedArrayPrototype%'),

    '%BigInt64ArrayPrototype%': TypedArrayPrototype('BigInt64Array'),
    '%BigUint64ArrayPrototype%': TypedArrayPrototype('BigUint64Array'),
    '%Float32ArrayPrototype%': TypedArrayPrototype('Float32Array'),
    '%Float64ArrayPrototype%': TypedArrayPrototype('Float64Array'),
    '%Int16ArrayPrototype%': TypedArrayPrototype('Int16Array'),
    '%Int32ArrayPrototype%': TypedArrayPrototype('Int32Array'),
    '%Int8ArrayPrototype%': TypedArrayPrototype('Int8Array'),
    '%Uint16ArrayPrototype%': TypedArrayPrototype('Uint16Array'),
    '%Uint32ArrayPrototype%': TypedArrayPrototype('Uint32Array'),
    '%Uint8ArrayPrototype%': TypedArrayPrototype('Uint8Array'),
    '%Uint8ClampedArrayPrototype%': TypedArrayPrototype('Uint8ClampedArray'),

    // *** Keyed Collections

    Map: {
      // Properties of the Map Constructor
      '[[Proto]]': '%FunctionPrototype%',
      '@@species': getter,
      prototype: '%MapPrototype%',
    },

    '%MapPrototype%': {
      clear: fn,
      constructor: 'Map',
      delete: fn,
      entries: fn,
      forEach: fn,
      get: fn,
      has: fn,
      keys: fn,
      set: fn,
      size: getter,
      values: fn,
      '@@iterator': fn,
      '@@toStringTag': 'string',
    },

    '%MapIteratorPrototype%': {
      // The %MapIteratorPrototype% Object
      '[[Proto]]': '%IteratorPrototype%',
      next: fn,
      '@@toStringTag': 'string',
    },

    Set: {
      // Properties of the Set Constructor
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%SetPrototype%',
      '@@species': getter,
    },

    '%SetPrototype%': {
      add: fn,
      clear: fn,
      constructor: 'Set',
      delete: fn,
      entries: fn,
      forEach: fn,
      has: fn,
      keys: fn,
      size: getter,
      values: fn,
      '@@iterator': fn,
      '@@toStringTag': 'string',
    },

    '%SetIteratorPrototype%': {
      // The %SetIteratorPrototype% Object
      '[[Proto]]': '%IteratorPrototype%',
      next: fn,
      '@@toStringTag': 'string',
    },

    WeakMap: {
      // Properties of the WeakMap Constructor
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%WeakMapPrototype%',
    },

    '%WeakMapPrototype%': {
      constructor: 'WeakMap',
      delete: fn,
      get: fn,
      has: fn,
      set: fn,
      '@@toStringTag': 'string',
    },

    WeakSet: {
      // Properties of the WeakSet Constructor
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%WeakSetPrototype%',
    },

    '%WeakSetPrototype%': {
      add: fn,
      constructor: 'WeakSet',
      delete: fn,
      has: fn,
      '@@toStringTag': 'string',
    },

    // *** Structured Data

    ArrayBuffer: {
      // Properties of the ArrayBuffer Constructor
      '[[Proto]]': '%FunctionPrototype%',
      isView: fn,
      prototype: '%ArrayBufferPrototype%',
      '@@species': getter,
      // See https://github.com/Moddable-OpenSource/moddable/issues/523
      fromString: false,
      // See https://github.com/Moddable-OpenSource/moddable/issues/523
      fromBigInt: false,
    },

    '%ArrayBufferPrototype%': {
      byteLength: getter,
      constructor: 'ArrayBuffer',
      slice: fn,
      '@@toStringTag': 'string',
      // See https://github.com/Moddable-OpenSource/moddable/issues/523
      concat: false,
    },

    // SharedArrayBuffer Objects
    SharedArrayBuffer: false, // UNSAFE and purposely suppressed.
    '%SharedArrayBufferPrototype%': false, // UNSAFE and purposely suppressed.

    DataView: {
      // Properties of the DataView Constructor
      '[[Proto]]': '%FunctionPrototype%',
      BYTES_PER_ELEMENT: 'number', // Non std but undeletable on Safari.
      prototype: '%DataViewPrototype%',
    },

    '%DataViewPrototype%': {
      buffer: getter,
      byteLength: getter,
      byteOffset: getter,
      constructor: 'DataView',
      getBigInt64: fn,
      getBigUint64: fn,
      getFloat32: fn,
      getFloat64: fn,
      getInt8: fn,
      getInt16: fn,
      getInt32: fn,
      getUint8: fn,
      getUint16: fn,
      getUint32: fn,
      setBigInt64: fn,
      setBigUint64: fn,
      setFloat32: fn,
      setFloat64: fn,
      setInt8: fn,
      setInt16: fn,
      setInt32: fn,
      setUint8: fn,
      setUint16: fn,
      setUint32: fn,
      '@@toStringTag': 'string',
    },

    // Atomics
    Atomics: false, // UNSAFE and suppressed.

    JSON: {
      parse: fn,
      stringify: fn,
      '@@toStringTag': 'string',
    },

    // *** Control Abstraction Objects

    '%IteratorPrototype%': {
      // The %IteratorPrototype% Object
      '@@iterator': fn,
    },

    '%AsyncIteratorPrototype%': {
      // The %AsyncIteratorPrototype% Object
      '@@asyncIterator': fn,
    },

    '%InertGeneratorFunction%': {
      // Properties of the GeneratorFunction Constructor
      '[[Proto]]': '%InertFunction%',
      prototype: '%Generator%',
    },

    '%Generator%': {
      // Properties of the GeneratorFunction Prototype Object
      '[[Proto]]': '%FunctionPrototype%',
      constructor: '%InertGeneratorFunction%',
      prototype: '%GeneratorPrototype%',
      '@@toStringTag': 'string',
    },

    '%InertAsyncGeneratorFunction%': {
      // Properties of the AsyncGeneratorFunction Constructor
      '[[Proto]]': '%InertFunction%',
      prototype: '%AsyncGenerator%',
    },

    '%AsyncGenerator%': {
      // Properties of the AsyncGeneratorFunction Prototype Object
      '[[Proto]]': '%FunctionPrototype%',
      constructor: '%InertAsyncGeneratorFunction%',
      prototype: '%AsyncGeneratorPrototype%',
      '@@toStringTag': 'string',
    },

    '%GeneratorPrototype%': {
      // Properties of the Generator Prototype Object
      '[[Proto]]': '%IteratorPrototype%',
      constructor: '%Generator%',
      next: fn,
      return: fn,
      throw: fn,
      '@@toStringTag': 'string',
    },

    '%AsyncGeneratorPrototype%': {
      // Properties of the AsyncGenerator Prototype Object
      '[[Proto]]': '%AsyncIteratorPrototype%',
      constructor: '%AsyncGenerator%',
      next: fn,
      return: fn,
      throw: fn,
      '@@toStringTag': 'string',
    },

    // TODO: To be replaced with Promise.delegate
    //
    // The HandledPromise global variable shimmed by `@agoric/eventual-send/shim`
    // implements an initial version of the eventual send specification at:
    // https://github.com/tc39/proposal-eventual-send
    //
    // We will likely change this to add a property to Promise called
    // Promise.delegate and put static methods on it, which will necessitate
    // another whitelist change to update to the current proposed standard.
    HandledPromise: {
      '[[Proto]]': 'Promise',
      applyFunction: fn,
      applyFunctionSendOnly: fn,
      applyMethod: fn,
      applyMethodSendOnly: fn,
      get: fn,
      getSendOnly: fn,
      prototype: '%PromisePrototype%',
      resolve: fn,
    },

    Promise: {
      // Properties of the Promise Constructor
      '[[Proto]]': '%FunctionPrototype%',
      all: fn,
      allSettled: fn,
      // To transition from `false` to `fn` once we also have `AggregateError`
      // TODO https://github.com/Agoric/SES-shim/issues/550
      any: false, // ES2021
      prototype: '%PromisePrototype%',
      race: fn,
      reject: fn,
      resolve: fn,
      '@@species': getter,
    },

    '%PromisePrototype%': {
      // Properties of the Promise Prototype Object
      catch: fn,
      constructor: 'Promise',
      finally: fn,
      then: fn,
      '@@toStringTag': 'string',
    },

    '%InertAsyncFunction%': {
      // Properties of the AsyncFunction Constructor
      '[[Proto]]': '%InertFunction%',
      prototype: '%AsyncFunctionPrototype%',
    },

    '%AsyncFunctionPrototype%': {
      // Properties of the AsyncFunction Prototype Object
      '[[Proto]]': '%FunctionPrototype%',
      constructor: '%InertAsyncFunction%',
      '@@toStringTag': 'string',
    },

    // Reflection

    Reflect: {
      // The Reflect Object
      // Not a function object.
      apply: fn,
      construct: fn,
      defineProperty: fn,
      deleteProperty: fn,
      get: fn,
      getOwnPropertyDescriptor: fn,
      getPrototypeOf: fn,
      has: fn,
      isExtensible: fn,
      ownKeys: fn,
      preventExtensions: fn,
      set: fn,
      setPrototypeOf: fn,
      '@@toStringTag': 'string',
    },

    Proxy: {
      // Properties of the Proxy Constructor
      '[[Proto]]': '%FunctionPrototype%',
      revocable: fn,
    },

    // Appendix B

    // Annex B: Additional Properties of the Global Object

    escape: fn,
    unescape: fn,

    // Proposed

    '%UniqueCompartment%': {
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%CompartmentPrototype%',
      toString: fn,
    },

    '%InertCompartment%': {
      '[[Proto]]': '%FunctionPrototype%',
      prototype: '%CompartmentPrototype%',
      toString: fn,
    },

    '%CompartmentPrototype%': {
      constructor: '%InertCompartment%',
      evaluate: fn,
      globalThis: getter,
      name: getter,
      // Should this be proposed?
      toString: fn,
      __isKnownScopeProxy__: fn,
    },

    lockdown: fn,
    harden: fn,

    '%InitialGetStackString%': fn,
  };

  // Like defineProperty, but throws if it would modify an existing property.
  // We use this to ensure that two conflicting attempts to define the same
  // property throws, causing SES initialization to fail. Otherwise, a
  // conflict between, for example, two of SES's internal whitelists might
  // get masked as one overwrites the other. Accordingly, the thrown error
  // complains of a "Conflicting definition".
  function initProperty(obj, name, desc) {
    if (objectHasOwnProperty(obj, name)) {
      const preDesc = getOwnPropertyDescriptor(obj, name);
      if (
        !Object.is(preDesc.value, desc.value) ||
        preDesc.get !== desc.get ||
        preDesc.set !== desc.set ||
        preDesc.writable !== desc.writable ||
        preDesc.enumerable !== desc.enumerable ||
        preDesc.configurable !== desc.configurable
      ) {
        throw new Error(`Conflicting definitions of ${name}`);
      }
    }
    defineProperty(obj, name, desc);
  }

  // Like defineProperties, but throws if it would modify an existing property.
  // This ensures that the intrinsics added to the intrinsics collector object
  // graph do not overlap.
  function initProperties(obj, descs) {
    for (const [name, desc] of entries(descs)) {
      initProperty(obj, name, desc);
    }
  }

  // sampleGlobals creates an intrinsics object, suitable for
  // interinsicsCollector.addIntrinsics, from the named properties of a global
  // object.
  function sampleGlobals(globalObject, newPropertyNames) {
    const newIntrinsics = { __proto__: null };
    for (const [globalName, intrinsicName] of entries(newPropertyNames)) {
      if (objectHasOwnProperty(globalObject, globalName)) {
        newIntrinsics[intrinsicName] = globalObject[globalName];
      }
    }
    return newIntrinsics;
  }

  function makeIntrinsicsCollector() {
    const intrinsics = { __proto__: null };
    let pseudoNatives;

    const intrinsicsCollector = {
      addIntrinsics(newIntrinsics) {
        initProperties(intrinsics, getOwnPropertyDescriptors(newIntrinsics));
      },

      // For each intrinsic, if it has a `.prototype` property, use the
      // whitelist to find out the intrinsic name for that prototype and add it
      // to the intrinsics.
      completePrototypes() {
        for (const [name, intrinsic] of entries(intrinsics)) {
          if (intrinsic !== Object(intrinsic)) {
            // eslint-disable-next-line no-continue
            continue;
          }
          if (!objectHasOwnProperty(intrinsic, 'prototype')) {
            // eslint-disable-next-line no-continue
            continue;
          }
          const permit = whitelist[name];
          if (typeof permit !== 'object') {
            throw new Error(`Expected permit object at whitelist.${name}`);
          }
          const namePrototype = permit.prototype;
          if (!namePrototype) {
            throw new Error(`${name}.prototype property not whitelisted`);
          }
          if (
            typeof namePrototype !== 'string' ||
            !objectHasOwnProperty(whitelist, namePrototype)
          ) {
            throw new Error(`Unrecognized ${name}.prototype whitelist entry`);
          }
          const intrinsicPrototype = intrinsic.prototype;
          if (objectHasOwnProperty(intrinsics, namePrototype)) {
            if (intrinsics[namePrototype] !== intrinsicPrototype) {
              throw new Error(`Conflicting bindings of ${namePrototype}`);
            }
            // eslint-disable-next-line no-continue
            continue;
          }
          intrinsics[namePrototype] = intrinsicPrototype;
        }
      },
      finalIntrinsics() {
        freeze(intrinsics);
        pseudoNatives = new WeakSet(
          values(intrinsics).filter(obj => typeof obj === 'function'),
        );
        return intrinsics;
      },
      isPseudoNative(obj) {
        if (!pseudoNatives) {
          throw new Error(
            'isPseudoNative can only be called after finalIntrinsics',
          );
        }
        return pseudoNatives.has(obj);
      },
    };

    intrinsicsCollector.addIntrinsics(constantProperties);
    intrinsicsCollector.addIntrinsics(
      sampleGlobals(globalThis, universalPropertyNames),
    );

    return intrinsicsCollector;
  }

  /**
   * getGlobalIntrinsics()
   * Doesn't tame, delete, or modify anything. Samples globalObject to create an
   * intrinsics record containing only the whitelisted global variables, listed
   * by the intrinsic names appropriate for new globals, i.e., the globals of
   * newly constructed compartments.
   *
   * WARNING:
   * If run before lockdown, the returned intrinsics record will carry the
   * *original* unsafe (feral, untamed) bindings of these global variables.
   *
   * @param {Object} globalObject
   */
  function getGlobalIntrinsics(globalObject) {
    const intrinsicsCollector = makeIntrinsicsCollector();

    intrinsicsCollector.addIntrinsics(
      sampleGlobals(globalObject, sharedGlobalPropertyNames),
    );

    return intrinsicsCollector.finalIntrinsics();
  }

  const InertCompartment = function Compartment(
    _endowments = {},
    _modules = {},
    _options = {},
  ) {
    throw new TypeError('Not available');
  };

  /**
   * Object.getConstructorOf()
   * Helper function to improve readability, similar to Object.getPrototypeOf().
   *
   * @param {Object} obj
   */
  function getConstructorOf(obj) {
    return getPrototypeOf(obj).constructor;
  }

  /**
   * getAnonymousIntrinsics()
   * Get the intrinsics not otherwise reachable by named own property
   * traversal from the global object.
   *
   * @returns {Object}
   */
  function getAnonymousIntrinsics() {
    const InertFunction = Function.prototype.constructor;

    const SymbolIterator = (typeof Symbol && Symbol.iterator) || '@@iterator';
    const SymbolMatchAll = (typeof Symbol && Symbol.matchAll) || '@@matchAll';

    // 9.2.4.1 %ThrowTypeError%

    // eslint-disable-next-line prefer-rest-params
    const ThrowTypeError = getOwnPropertyDescriptor(arguments, 'callee').get;

    // 21.1.5.2 The %StringIteratorPrototype% Object

    // eslint-disable-next-line no-new-wrappers
    const StringIteratorObject = new String()[SymbolIterator]();
    const StringIteratorPrototype = getPrototypeOf(StringIteratorObject);

    // 21.2.7.1 The %RegExpStringIteratorPrototype% Object
    const RegExpStringIterator =
      RegExp.prototype[SymbolMatchAll] && new RegExp()[SymbolMatchAll]();
    const RegExpStringIteratorPrototype =
      RegExpStringIterator && getPrototypeOf(RegExpStringIterator);

    // 22.1.5.2 The %ArrayIteratorPrototype% Object

    // eslint-disable-next-line no-array-constructor
    const ArrayIteratorObject = new Array()[SymbolIterator]();
    const ArrayIteratorPrototype = getPrototypeOf(ArrayIteratorObject);

    // 22.2.1 The %TypedArray% Intrinsic Object

    const TypedArray = getPrototypeOf(Float32Array);

    // 23.1.5.2 The %MapIteratorPrototype% Object

    const MapIteratorObject = new Map()[SymbolIterator]();
    const MapIteratorPrototype = getPrototypeOf(MapIteratorObject);

    // 23.2.5.2 The %SetIteratorPrototype% Object

    const SetIteratorObject = new Set()[SymbolIterator]();
    const SetIteratorPrototype = getPrototypeOf(SetIteratorObject);

    // 25.1.2 The %IteratorPrototype% Object

    const IteratorPrototype = getPrototypeOf(ArrayIteratorPrototype);

    // 25.2.1 The GeneratorFunction Constructor

    // eslint-disable-next-line no-empty-function
    function* GeneratorFunctionInstance() {}
    const GeneratorFunction = getConstructorOf(GeneratorFunctionInstance);

    // 25.2.3 Properties of the GeneratorFunction Prototype Object

    const Generator = GeneratorFunction.prototype;

    // 25.3.1 The AsyncGeneratorFunction Constructor

    // eslint-disable-next-line no-empty-function
    async function* AsyncGeneratorFunctionInstance() {}
    const AsyncGeneratorFunction = getConstructorOf(
      AsyncGeneratorFunctionInstance,
    );

    // 25.3.2.2 AsyncGeneratorFunction.prototype
    const AsyncGenerator = AsyncGeneratorFunction.prototype;
    // 25.5.1 Properties of the AsyncGenerator Prototype Object
    const AsyncGeneratorPrototype = AsyncGenerator.prototype;
    const AsyncIteratorPrototype = getPrototypeOf(AsyncGeneratorPrototype);

    // 25.7.1 The AsyncFunction Constructor

    // eslint-disable-next-line no-empty-function
    async function AsyncFunctionInstance() {}
    const AsyncFunction = getConstructorOf(AsyncFunctionInstance);

    const intrinsics = {
      '%InertFunction%': InertFunction,
      '%ArrayIteratorPrototype%': ArrayIteratorPrototype,
      '%InertAsyncFunction%': AsyncFunction,
      '%AsyncGenerator%': AsyncGenerator,
      '%InertAsyncGeneratorFunction%': AsyncGeneratorFunction,
      '%AsyncGeneratorPrototype%': AsyncGeneratorPrototype,
      '%AsyncIteratorPrototype%': AsyncIteratorPrototype,
      '%Generator%': Generator,
      '%InertGeneratorFunction%': GeneratorFunction,
      '%IteratorPrototype%': IteratorPrototype,
      '%MapIteratorPrototype%': MapIteratorPrototype,
      '%RegExpStringIteratorPrototype%': RegExpStringIteratorPrototype,
      '%SetIteratorPrototype%': SetIteratorPrototype,
      '%StringIteratorPrototype%': StringIteratorPrototype,
      '%ThrowTypeError%': ThrowTypeError,
      '%TypedArray%': TypedArray,
      '%InertCompartment%': InertCompartment,
    };

    return intrinsics;
  }

  // Adapted from SES/Caja - Copyright (C) 2011 Google Inc.
  // Copyright (C) 2018 Agoric

  // Licensed under the Apache License, Version 2.0 (the "License");
  // you may not use this file except in compliance with the License.
  // You may obtain a copy of the License at
  //
  // http://www.apache.org/licenses/LICENSE-2.0
  //
  // Unless required by applicable law or agreed to in writing, software
  // distributed under the License is distributed on an "AS IS" BASIS,
  // WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  // See the License for the specific language governing permissions and
  // limitations under the License.

  // based upon:
  // https://github.com/google/caja/blob/master/src/com/google/caja/ses/startSES.js
  // https://github.com/google/caja/blob/master/src/com/google/caja/ses/repairES5.js
  // then copied from proposal-frozen-realms deep-freeze.js
  // then copied from SES/src/bundle/deepFreeze.js

  // @ts-check

  const { freeze: freeze$1, getOwnPropertyDescriptors: getOwnPropertyDescriptors$1, getPrototypeOf: getPrototypeOf$1 } = Object;
  const { ownKeys } = Reflect;

  /**
   * @typedef {<T>(root: T) => T} Hardener
   */

  /**
   * Create a `harden` function.
   *
   * @returns {Hardener}
   */
  function makeHardener() {
    const hardened = new WeakSet();

    const { harden } = {
      /**
       * @template T
       * @param {T} root
       * @returns {T}
       */
      harden(root) {
        const toFreeze = new Set();
        const paths = new WeakMap();

        // If val is something we should be freezing but aren't yet,
        // add it to toFreeze.
        /**
         * @param {any} val
         * @param {string} [path]
         */
        function enqueue(val, path = undefined) {
          if (Object(val) !== val) {
            // ignore primitives
            return;
          }
          const type = typeof val;
          if (type !== 'object' && type !== 'function') {
            // future proof: break until someone figures out what it should do
            throw new TypeError(`Unexpected typeof: ${type}`);
          }
          if (hardened.has(val) || toFreeze.has(val)) {
            // Ignore if this is an exit, or we've already visited it
            return;
          }
          // console.log(`adding ${val} to toFreeze`, val);
          toFreeze.add(val);
          paths.set(val, path);
        }

        /**
         * @param {any} obj
         */
        function freezeAndTraverse(obj) {
          // Now freeze the object to ensure reactive
          // objects such as proxies won't add properties
          // during traversal, before they get frozen.

          // Object are verified before being enqueued,
          // therefore this is a valid candidate.
          // Throws if this fails (strict mode).
          freeze$1(obj);

          // we rely upon certain commitments of Object.freeze and proxies here

          // get stable/immutable outbound links before a Proxy has a chance to do
          // something sneaky.
          const path = paths.get(obj) || 'unknown';
          const descs = getOwnPropertyDescriptors$1(obj);
          const proto = getPrototypeOf$1(obj);
          enqueue(proto, `${path}.__proto__`);

          ownKeys(descs).forEach(name => {
            const pathname = `${path}.${String(name)}`;
            // todo uncurried form
            // todo: getOwnPropertyDescriptors is guaranteed to return well-formed
            // descriptors, but they still inherit from Object.prototype. If
            // someone has poisoned Object.prototype to add 'value' or 'get'
            // properties, then a simple 'if ("value" in desc)' or 'desc.value'
            // test could be confused. We use hasOwnProperty to be sure about
            // whether 'value' is present or not, which tells us for sure that
            // this is a data property.
            // The 'name' may be a symbol, and TypeScript doesn't like us to
            // index arbitrary symbols on objects, so we pretend they're just
            // strings.
            const desc = descs[/** @type {string} */ (name)];
            if ('value' in desc) {
              // todo uncurried form
              enqueue(desc.value, `${pathname}`);
            } else {
              enqueue(desc.get, `${pathname}(get)`);
              enqueue(desc.set, `${pathname}(set)`);
            }
          });
        }

        function dequeue() {
          // New values added before forEach() has finished will be visited.
          toFreeze.forEach(freezeAndTraverse); // todo curried forEach
        }

        function commit() {
          // todo curried forEach
          // we capture the real WeakSet.prototype.add above, in case someone
          // changes it. The two-argument form of forEach passes the second
          // argument as the 'this' binding, so we add to the correct set.
          toFreeze.forEach(hardened.add, hardened);
        }

        enqueue(root);
        dequeue();
        // console.log("toFreeze set:", toFreeze);
        commit();

        return root;
      },
    };

    return harden;
  }

  // Copyright (C) 2011 Google Inc.

  const { apply: apply$1, ownKeys: ownKeys$1 } = Reflect;
  const uncurryThis$1 = fn => (thisArg, ...args) => apply$1(fn, thisArg, args);
  const hasOwnProperty = uncurryThis$1(Object.prototype.hasOwnProperty);

  /**
   * asStringPropertyName()
   *
   * @param {string} path
   * @param {string | symbol} prop
   */
  function asStringPropertyName(path, prop) {
    if (typeof prop === 'string') {
      return prop;
    }

    if (typeof prop === 'symbol') {
      return `@@${prop.toString().slice(14, -1)}`;
    }

    throw new TypeError(`Unexpected property name type ${path} ${prop}`);
  }

  /**
   * whitelistIntrinsics()
   * Removes all non-whitelisted properties found by recursively and
   * reflectively walking own property chains.
   *
   * @param {Object} intrinsics
   * @param {(Object) => void} nativeBrander
   */
  function whitelistIntrinsics(intrinsics, nativeBrander) {
    // These primities are allowed allowed for permits.
    const primitives = ['undefined', 'boolean', 'number', 'string', 'symbol'];

    /*
     * whitelistPrototype()
     * Validate the object's [[prototype]] against a permit.
     */
    function whitelistPrototype(path, obj, protoName) {
      if (obj !== Object(obj)) {
        throw new TypeError(`Object expected: ${path}, ${obj}, ${protoName}`);
      }
      const proto = getPrototypeOf(obj);

      // Null prototype.
      if (proto === null && protoName === null) {
        return;
      }

      // Assert: protoName, if provided, is a string.
      if (protoName !== undefined && typeof protoName !== 'string') {
        throw new TypeError(`Malformed whitelist permit ${path}.__proto__`);
      }

      // If permit not specified, default to Object.prototype.
      if (proto === intrinsics[protoName || '%ObjectPrototype%']) {
        return;
      }

      // We can't clean [[prototype]], therefore abort.
      throw new Error(`Unexpected intrinsic ${path}.__proto__ at ${protoName}`);
    }

    /*
     * isWhitelistPropertyValue()
     * Whitelist a single property value against a permit.
     */
    function isWhitelistPropertyValue(path, value, prop, permit) {
      if (typeof permit === 'object') {
        // eslint-disable-next-line no-use-before-define
        whitelistProperties(path, value, permit);
        // The property is whitelisted.
        return true;
      }

      if (permit === false) {
        // A boolan 'false' permit specifies the removal of a property.
        // We require a more specific permit instead of allowing 'true'.
        return false;
      }

      if (typeof permit === 'string') {
        // A string permit can have one of two meanings:

        if (prop === 'prototype' || prop === 'constructor') {
          // For prototype and constructor value properties, the permit
          // is the name of an intrinsic.
          // Assumption: prototype and constructor cannot be primitives.
          // Assert: the permit is the name of an intrinsic.
          // Assert: the property value is equal to that intrinsic.

          if (hasOwnProperty(intrinsics, permit)) {
            if (value !== intrinsics[permit]) {
              throw new TypeError(`Does not match whitelist ${path}`);
            }
            return true;
          }
        } else {
          // For all other properties, the permit is the name of a primitive.
          // Assert: the permit is the name of a primitive.
          // Assert: the property value type is equal to that primitive.

          // eslint-disable-next-line no-lonely-if
          if (primitives.includes(permit)) {
            // eslint-disable-next-line valid-typeof
            if (typeof value !== permit) {
              throw new TypeError(
                `At ${path} expected ${permit} not ${typeof value}`,
              );
            }
            return true;
          }
        }
      }

      throw new TypeError(`Unexpected whitelist permit ${permit} at ${path}`);
    }

    /*
     * isWhitelistProperty()
     * Whitelist a single property against a permit.
     */
    function isWhitelistProperty(path, obj, prop, permit) {
      const desc = getOwnPropertyDescriptor(obj, prop);

      // Is this a value property?
      if (hasOwnProperty(desc, 'value')) {
        if (isAccessorPermit(permit)) {
          throw new TypeError(`Accessor expected at ${path}`);
        }
        return isWhitelistPropertyValue(path, desc.value, prop, permit);
      }
      if (!isAccessorPermit(permit)) {
        throw new TypeError(`Accessor not expected at ${path}`);
      }
      return (
        isWhitelistPropertyValue(`${path}<get>`, desc.get, prop, permit.get) &&
        isWhitelistPropertyValue(`${path}<set>`, desc.set, prop, permit.set)
      );
    }

    /*
     * getSubPermit()
     */
    function getSubPermit(obj, permit, prop) {
      const permitProp = prop === '__proto__' ? '--proto--' : prop;
      if (hasOwnProperty(permit, permitProp)) {
        return permit[permitProp];
      }

      if (typeof obj === 'function') {
        nativeBrander(obj);
        if (hasOwnProperty(FunctionInstance, permitProp)) {
          return FunctionInstance[permitProp];
        }
      }

      return undefined;
    }

    /*
     * whitelistProperties()
     * Whitelist all properties against a permit.
     */
    function whitelistProperties(path, obj, permit) {
      if (obj === undefined) {
        return;
      }

      const protoName = permit['[[Proto]]'];
      whitelistPrototype(path, obj, protoName);

      for (const prop of ownKeys$1(obj)) {
        const propString = asStringPropertyName(path, prop);
        const subPath = `${path}.${propString}`;
        const subPermit = getSubPermit(obj, permit, propString);

        if (subPermit) {
          // Property has a permit.
          if (isWhitelistProperty(subPath, obj, prop, subPermit)) {
            // Property is whitelisted.
            // eslint-disable-next-line no-continue
            continue;
          }
        }

        if (subPermit !== false) {
          // This call to `console.log` is intensional. It is not a vestige
          // of a debugging attempt. See the comment at top of file for an
          // explanation.
          console.log(`Removing ${subPath}`);
        }
        try {
          delete obj[prop];
        } catch (err) {
          if (prop in obj) {
            console.error(`failed to delete ${subPath}`, err);
          } else {
            console.error(`deleting ${subPath} threw`, err);
          }
          throw err;
        }
      }
    }

    // Start path with 'intrinsics' to clarify that properties are not
    // removed from the global object by the whitelisting operation.
    whitelistProperties('intrinsics', intrinsics, whitelist);
  }

  // Adapted from SES/Caja - Copyright (C) 2011 Google Inc.

  /**
   * Replace the legacy accessors of Object to comply with strict mode
   * and ES2016 semantics, we do this by redefining them while in 'use strict'.
   *
   * todo: list the issues resolved
   *
   * This function can be used in two ways: (1) invoked directly to fix the primal
   * realm's Object.prototype, and (2) converted to a string to be executed
   * inside each new RootRealm to fix their Object.prototypes. Evaluation requires
   * the function to have no dependencies, so don't import anything from
   * the outside.
   */

  function repairLegacyAccessors() {
    try {
      // Verify that the method is not callable.
      // eslint-disable-next-line no-underscore-dangle
      (0, Object.prototype.__lookupGetter__)('x');
    } catch (ignore) {
      // Throws, no need to patch.
      return;
    }

    // On some platforms, the implementation of these functions act as
    // if they are in sloppy mode: if they're invoked badly, they will
    // expose the global object, so we need to repair these for
    // security. Thus it is our responsibility to fix this, and we need
    // to include repairAccessors. E.g. Chrome in 2016.

    function toObject(obj) {
      if (obj === undefined || obj === null) {
        throw new TypeError("can't convert undefined or null to object");
      }
      return Object(obj);
    }

    function asPropertyName(obj) {
      if (typeof obj === 'symbol') {
        return obj;
      }
      return `${obj}`;
    }

    function aFunction(obj, accessor) {
      if (typeof obj !== 'function') {
        throw TypeError(`invalid ${accessor} usage`);
      }
      return obj;
    }

    defineProperties(objectPrototype, {
      __defineGetter__: {
        value: function __defineGetter__(prop, func) {
          const O = toObject(this);
          defineProperty(O, prop, {
            get: aFunction(func, 'getter'),
            enumerable: true,
            configurable: true,
          });
        },
      },
      __defineSetter__: {
        value: function __defineSetter__(prop, func) {
          const O = toObject(this);
          defineProperty(O, prop, {
            set: aFunction(func, 'setter'),
            enumerable: true,
            configurable: true,
          });
        },
      },
      __lookupGetter__: {
        value: function __lookupGetter__(prop) {
          let O = toObject(this);
          prop = asPropertyName(prop);
          let desc;
          // eslint-disable-next-line no-cond-assign
          while (O && !(desc = getOwnPropertyDescriptor(O, prop))) {
            O = getPrototypeOf(O);
          }
          return desc && desc.get;
        },
      },
      __lookupSetter__: {
        value: function __lookupSetter__(prop) {
          let O = toObject(this);
          prop = asPropertyName(prop);
          let desc;
          // eslint-disable-next-line no-cond-assign
          while (O && !(desc = getOwnPropertyDescriptor(O, prop))) {
            O = getPrototypeOf(O);
          }
          return desc && desc.set;
        },
      },
    });
  }

  // This module replaces the original `Function` constructor, and the original
  // `%GeneratorFunction%`, `%AsyncFunction%` and `%AsyncGeneratorFunction%`,
  // with safe replacements that throw if invoked.
  //
  // These are all reachable via syntax, so it isn't sufficient to just
  // replace global properties with safe versions. Our main goal is to prevent
  // access to the `Function` constructor through these starting points.
  //
  // After modules block is done, the originals must no longer be reachable,
  // unless a copy has been made, and functions can only be created by syntax
  // (using eval) or by invoking a previously saved reference to the originals.
  //
  // Typically, this module will not be used directly, but via the
  // [lockdown - shim] which handles all necessary repairs and taming in SES.
  //
  // Relation to ECMA specifications
  //
  // The taming of constructors really wants to be part of the standard, because
  // new constructors may be added in the future, reachable from syntax, and this
  // list must be updated to match.
  //
  // In addition, the standard needs to define four new intrinsics for the safe
  // replacement functions. See [./whitelist intrinsics].
  //
  // Adapted from SES/Caja
  // Copyright (C) 2011 Google Inc.
  // https://github.com/google/caja/blob/master/src/com/google/caja/ses/startSES.js
  // https://github.com/google/caja/blob/master/src/com/google/caja/ses/repairES5.js

  /**
   * tameFunctionConstructors()
   * This block replaces the original Function constructor, and the original
   * %GeneratorFunction% %AsyncFunction% and %AsyncGeneratorFunction%, with
   * safe replacements that throw if invoked.
   */
  function tameFunctionConstructors() {
    try {
      // Verify that the method is not callable.
      (0, Function.prototype.constructor)('return 1');
    } catch (ignore) {
      // Throws, no need to patch.
      return {};
    }

    const newIntrinsics = {};

    /*
     * The process to repair constructors:
     * 1. Create an instance of the function by evaluating syntax
     * 2. Obtain the prototype from the instance
     * 3. Create a substitute tamed constructor
     * 4. Replace the original constructor with the tamed constructor
     * 5. Replace tamed constructor prototype property with the original one
     * 6. Replace its [[Prototype]] slot with the tamed constructor of Function
     */
    function repairFunction(name, intrinsicName, declaration) {
      let FunctionInstance;
      try {
        // eslint-disable-next-line no-eval
        FunctionInstance = (0, eval)(declaration);
      } catch (e) {
        if (e instanceof SyntaxError) {
          // Prevent failure on platforms where async and/or generators
          // are not supported.
          return;
        }
        // Re-throw
        throw e;
      }
      const FunctionPrototype = getPrototypeOf(FunctionInstance);

      // Prevents the evaluation of source when calling constructor on the
      // prototype of functions.
      // eslint-disable-next-line func-names
      const InertConstructor = function() {
        throw new TypeError('Not available');
      };
      defineProperties(InertConstructor, {
        prototype: { value: FunctionPrototype },
        name: {
          value: name,
          writable: false,
          enumerable: false,
          configurable: true,
        },
      });

      defineProperties(FunctionPrototype, {
        constructor: { value: InertConstructor },
      });

      // Reconstructs the inheritance among the new tamed constructors
      // to mirror the original specified in normal JS.
      if (InertConstructor !== Function.prototype.constructor) {
        setPrototypeOf(InertConstructor, Function.prototype.constructor);
      }

      newIntrinsics[intrinsicName] = InertConstructor;
    }

    // Here, the order of operation is important: Function needs to be repaired
    // first since the other repaired constructors need to inherit from the
    // tamed Function function constructor.

    repairFunction('Function', '%InertFunction%', '(function(){})');
    repairFunction(
      'GeneratorFunction',
      '%InertGeneratorFunction%',
      '(function*(){})',
    );
    repairFunction(
      'AsyncFunction',
      '%InertAsyncFunction%',
      '(async function(){})',
    );
    repairFunction(
      'AsyncGeneratorFunction',
      '%InertAsyncGeneratorFunction%',
      '(async function*(){})',
    );

    return newIntrinsics;
  }

  function tameDateConstructor(dateTaming = 'safe') {
    if (dateTaming !== 'safe' && dateTaming !== 'unsafe') {
      throw new Error(`unrecognized dateTaming ${dateTaming}`);
    }
    const OriginalDate = Date;
    const DatePrototype = OriginalDate.prototype;

    // Use concise methods to obtain named functions without constructors.
    const tamedMethods = {
      now() {
        return NaN;
      },
    };

    // Tame the Date constructor.
    // Common behavior
    //   * new Date(x) coerces x into a number and then returns a Date
    //     for that number of millis since the epoch
    //   * new Date(NaN) returns a Date object which stringifies to
    //     'Invalid Date'
    //   * new Date(undefined) returns a Date object which stringifies to
    //     'Invalid Date'
    // OriginalDate (normal standard) behavior
    //   * Date(anything) gives a string with the current time
    //   * new Date() returns the current time, as a Date object
    // SharedDate behavior
    //   * Date(anything) returned 'Invalid Date'
    //   * new Date() returns a Date object which stringifies to
    //     'Invalid Date'
    const makeDateConstructor = ({ powers = 'none' } = {}) => {
      let ResultDate;
      if (powers === 'original') {
        ResultDate = function Date(...rest) {
          if (new.target === undefined) {
            return Reflect.apply(OriginalDate, undefined, rest);
          }
          return Reflect.construct(OriginalDate, rest, new.target);
        };
      } else {
        ResultDate = function Date(...rest) {
          if (new.target === undefined) {
            return 'Invalid Date';
          }
          if (rest.length === 0) {
            rest = [NaN];
          }
          return Reflect.construct(OriginalDate, rest, new.target);
        };
      }

      defineProperties(ResultDate, {
        length: { value: 7 },
        prototype: {
          value: DatePrototype,
          writable: false,
          enumerable: false,
          configurable: false,
        },
        parse: {
          value: Date.parse,
          writable: true,
          enumerable: false,
          configurable: true,
        },
        UTC: {
          value: Date.UTC,
          writable: true,
          enumerable: false,
          configurable: true,
        },
      });
      return ResultDate;
    };
    const InitialDate = makeDateConstructor({ powers: 'original' });
    const SharedDate = makeDateConstructor({ power: 'none' });

    defineProperties(InitialDate, {
      now: {
        value: Date.now,
        writable: true,
        enumerable: false,
        configurable: true,
      },
    });
    defineProperties(SharedDate, {
      now: {
        value: tamedMethods.now,
        writable: true,
        enumerable: false,
        configurable: true,
      },
    });

    defineProperties(DatePrototype, {
      constructor: { value: SharedDate },
    });

    return {
      '%InitialDate%': InitialDate,
      '%SharedDate%': SharedDate,
    };
  }

  function tameMathObject(mathTaming = 'safe') {
    if (mathTaming !== 'safe' && mathTaming !== 'unsafe') {
      throw new Error(`unrecognized mathTaming ${mathTaming}`);
    }
    const originalMath = Math;
    const initialMath = originalMath; // to follow the naming pattern

    const { random: _, ...otherDescriptors } = getOwnPropertyDescriptors(
      originalMath,
    );

    const sharedMath = create(Object.prototype, otherDescriptors);

    return {
      '%InitialMath%': initialMath,
      '%SharedMath%': sharedMath,
    };
  }

  function tameRegExpConstructor(regExpTaming = 'safe') {
    if (regExpTaming !== 'safe' && regExpTaming !== 'unsafe') {
      throw new Error(`unrecognized regExpTaming ${regExpTaming}`);
    }
    const OriginalRegExp = RegExp;
    const RegExpPrototype = OriginalRegExp.prototype;

    const makeRegExpConstructor = (_ = {}) => {
      // RegExp has non-writable static properties we need to omit.
      const ResultRegExp = function RegExp(...rest) {
        if (new.target === undefined) {
          return OriginalRegExp(...rest);
        }
        return Reflect.construct(OriginalRegExp, rest, new.target);
      };

      defineProperties(ResultRegExp, {
        length: { value: 2 },
        prototype: {
          value: RegExpPrototype,
          writable: false,
          enumerable: false,
          configurable: false,
        },
        [Symbol.species]: getOwnPropertyDescriptor(
          OriginalRegExp,
          Symbol.species,
        ),
      });
      return ResultRegExp;
    };

    const InitialRegExp = makeRegExpConstructor();
    const SharedRegExp = makeRegExpConstructor();

    if (regExpTaming !== 'unsafe') {
      delete RegExpPrototype.compile;
    }
    defineProperties(RegExpPrototype, {
      constructor: { value: SharedRegExp },
    });

    return {
      '%InitialRegExp%': InitialRegExp,
      '%SharedRegExp%': SharedRegExp,
    };
  }

  /**
   * @file Exports {@code enablements}, a recursively defined
   * JSON record defining the optimum set of intrinsics properties
   * that need to be "repaired" before hardening is applied on
   * enviromments subject to the override mistake.
   *
   * @author JF Paradis
   * @author Mark S. Miller
   */

  /**
   * <p>Because "repairing" replaces data properties with accessors, every
   * time a repaired property is accessed, the associated getter is invoked,
   * which degrades the runtime performance of all code executing in the
   * repaired enviromment, compared to the non-repaired case. In order
   * to maintain performance, we only repair the properties of objects
   * for which hardening causes a breakage of their normal intended usage.
   *
   * There are three unwanted cases:
   * <ul>
   * <li>Overriding properties on objects typically used as records,
   *     namely {@code "Object"} and {@code "Array"}. In the case of arrays,
   *     the situation is unintentional, a given program might not be aware
   *     that non-numerical properties are stored on the underlying object
   *     instance, not on the array. When an object is typically used as a
   *     map, we repair all of its prototype properties.
   * <li>Overriding properties on objects that provide defaults on their
   *     prototype and that programs typically set using an assignment, such as
   *     {@code "Error.prototype.message"} and {@code "Function.prototype.name"}
   *     (both default to "").
   * <li>Setting-up a prototype chain, where a constructor is set to extend
   *     another one. This is typically set by assignment, for example
   *     {@code "Child.prototype.constructor = Child"}, instead of invoking
   *     Object.defineProperty();
   *
   * <p>Each JSON record enumerates the disposition of the properties on
   * some corresponding intrinsic object.
   *
   * <p>For each such record, the values associated with its property
   * names can be:
   * <ul>
   * <li>true, in which case this property is simply repaired. The
   *     value associated with that property is not traversed. For
   * 	   example, {@code "Function.prototype.name"} leads to true,
   *     meaning that the {@code "name"} property of {@code
   *     "Function.prototype"} should be repaired (which is needed
   *     when inheriting from @code{Function} and setting the subclass's
   *     {@code "prototype.name"} property). If the property is
   *     already an accessor property, it is not repaired (because
   *     accessors are not subject to the override mistake).
   * <li>"*", in which case this property is not repaired but the
   *     value associated with that property are traversed and repaired.
   * <li>Another record, in which case this property is not repaired
   *     and that next record represents the disposition of the object
   *     which is its value. For example,{@code "FunctionPrototype"}
   *     leads to another record explaining which properties {@code
   *     Function.prototype} need to be repaired.
   */
  const moderateEnablements = {
    '%ObjectPrototype%': {
      // Acorn 7 does override `constructor` by assignment, but
      // this is fixed as of acorn 8. Including the commented out
      // line below in this list confuses the Node console.
      // See https://github.com/Agoric/agoric-sdk/issues/2324
      //
      // So please update all
      // acorn dependencies to at least 8 instead. We are unable to do
      // so at this time due to a dependency via rollup. Instead we
      // do a post-install patch of acorn.
      // See https://github.com/Agoric/SES-shim/pull/588
      // If you are similarly stuck, do likewise. Or uncomment out
      // the following line and let us know why. The only known
      // cost is the ugly display from the Node console.
      //
      // constructor: true, // set by acorn 7, d3-color

      // As explained at
      // https://github.com/vega/vega/issues/3075
      // vega overrides `Object.prototype.hasOwnProperty` by
      // assignment. Those running into this should consider applying
      // the patch
      // https://github.com/Agoric/agoric-sdk/blob/master/patches/vega-util%2B1.16.0.patch
      // as we do, or
      // https://github.com/vega/vega/pull/3109/commits/50741c7e9035c407205ae45983470b8cb27c2da7
      // The owner of vega is aware of the concern, so this
      // may eventually be fixed at the source.
      // hasOwnProperty: true, // set by "vega-util".

      toString: true,
      valueOf: true,
    },

    '%ArrayPrototype%': {
      toString: true,
      push: true, // set by "Google Analytics"
    },

    // Function.prototype has no 'prototype' property to enable.
    // Function instances have their own 'name' and 'length' properties
    // which are configurable and non-writable. Thus, they are already
    // non-assignable anyway.
    '%FunctionPrototype%': {
      constructor: true, // set by "regenerator-runtime"
      bind: true, // set by "underscore", "express"
      toString: true, // set by "rollup"
    },

    '%ErrorPrototype%': {
      constructor: true, // set by "fast-json-patch", "node-fetch"
      message: true,
      name: true, // set by "precond", "ava", "node-fetch"
      toString: true, // set by "bluebird"
    },

    '%TypeErrorPrototype%': {
      constructor: true, // set by "readable-stream"
      message: true, // set by "tape"
      name: true, // set by "readable-stream"
    },

    '%SyntaxErrorPrototype%': {
      message: true, // to match TypeErrorPrototype.message
    },

    '%RangeErrorPrototype%': {
      message: true, // to match TypeErrorPrototype.message
    },

    '%URIErrorPrototype%': {
      message: true, // to match TypeErrorPrototype.message
    },

    '%EvalErrorPrototype%': {
      message: true, // to match TypeErrorPrototype.message
    },

    '%ReferenceErrorPrototype%': {
      message: true, // to match TypeErrorPrototype.message
    },

    '%PromisePrototype%': {
      constructor: true, // set by "core-js"
    },

    '%TypedArrayPrototype%': '*', // set by https://github.com/feross/buffer

    '%Generator%': {
      constructor: true,
      name: true,
      toString: true,
    },

    '%IteratorPrototype%': {
      toString: true,
    },
  };

  const minEnablements = {
    '%ObjectPrototype%': {
      toString: true,
    },

    '%FunctionPrototype%': {
      toString: true, // set by "rollup"
    },

    '%ErrorPrototype%': {
      name: true, // set by "precond", "ava", "node-fetch"
    },
  };

  // Adapted from SES/Caja

  const { ownKeys: ownKeys$2 } = Reflect;

  function isObject(obj) {
    return obj !== null && typeof obj === 'object';
  }

  /**
   * For a special set of properties defined in the `enablement` whitelist,
   * `enablePropertyOverrides` ensures that the effect of freezing does not
   * suppress the ability to override these properties on derived objects by
   * simple assignment.
   *
   * Because of lack of sufficient foresight at the time, ES5 unfortunately
   * specified that a simple assignment to a non-existent property must fail if
   * it would override an non-writable data property of the same name in the
   * shadow of the prototype chain. In retrospect, this was a mistake, the
   * so-called "override mistake". But it is now too late and we must live with
   * the consequences.
   *
   * As a result, simply freezing an object to make it tamper proof has the
   * unfortunate side effect of breaking previously correct code that is
   * considered to have followed JS best practices, if this previous code used
   * assignment to override.
   *
   * For the enabled properties, `enablePropertyOverrides` effectively shims what
   * the assignment behavior would have been in the absence of the override
   * mistake. However, the shim produces an imperfect emulation. It shims the
   * behavior by turning these data properties into accessor properties, where
   * the accessor's getter and setter provide the desired behavior. For
   * non-reflective operations, the illusion is perfect. However, reflective
   * operations like `getOwnPropertyDescriptor` see the descriptor of an accessor
   * property rather than the descriptor of a data property. At the time of this
   * writing, this is the best we know how to do.
   *
   * To the getter of the accessor we add a property named
   * `'originalValue'` whose value is, as it says, the value that the
   * data property had before being converted to an accessor property. We add
   * this extra property to the getter for two reason:
   *
   * The harden algorithm walks the own properties reflectively, i.e., with
   * `getOwnPropertyDescriptor` semantics, rather than `[[Get]]` semantics. When
   * it sees an accessor property, it does not invoke the getter. Rather, it
   * proceeds to walk both the getter and setter as part of its transitive
   * traversal. Without this extra property, `enablePropertyOverrides` would have
   * hidden the original data property value from `harden`, which would be bad.
   * Instead, by exposing that value in an own data property on the getter,
   * `harden` finds and walks it anyway.
   *
   * We enable a form of cooperative emulation, giving reflective code an
   * opportunity to cooperate in upholding the illusion. When such cooperative
   * reflective code sees an accessor property, where the accessor's getter
   * has an `originalValue` property, it knows that the getter is
   * alleging that it is the result of the `enablePropertyOverrides` conversion
   * pattern, so it can decide to cooperatively "pretend" that it sees a data
   * property with that value.
   *
   * @param {Record<string, any>} intrinsics
   * @param {'min' | 'moderate'} overrideTaming
   */
  function enablePropertyOverrides(intrinsics, overrideTaming) {
    function enable(path, obj, prop, desc) {
      if ('value' in desc && desc.configurable) {
        const { value } = desc;

        function getter() {
          return value;
        }
        defineProperty(getter, 'originalValue', {
          value,
          writable: false,
          enumerable: false,
          configurable: false,
        });

        function setter(newValue) {
          if (obj === this) {
            throw new TypeError(
              `Cannot assign to read only property '${String(
              prop,
            )}' of '${path}'`,
            );
          }
          if (objectHasOwnProperty(this, prop)) {
            this[prop] = newValue;
          } else {
            defineProperty(this, prop, {
              value: newValue,
              writable: true,
              enumerable: true,
              configurable: true,
            });
          }
        }

        defineProperty(obj, prop, {
          get: getter,
          set: setter,
          enumerable: desc.enumerable,
          configurable: desc.configurable,
        });
      }
    }

    function enableProperty(path, obj, prop) {
      const desc = getOwnPropertyDescriptor(obj, prop);
      if (!desc) {
        return;
      }
      enable(path, obj, prop, desc);
    }

    function enableAllProperties(path, obj) {
      const descs = getOwnPropertyDescriptors(obj);
      if (!descs) {
        return;
      }
      // TypeScript does not allow symbols to be used as indexes because it
      // cannot recokon types of symbolized properties.
      // @ts-ignore
      ownKeys$2(descs).forEach(prop => enable(path, obj, prop, descs[prop]));
    }

    function enableProperties(path, obj, plan) {
      for (const prop of getOwnPropertyNames(plan)) {
        const desc = getOwnPropertyDescriptor(obj, prop);
        if (!desc || desc.get || desc.set) {
          // No not a value property, nothing to do.
          // eslint-disable-next-line no-continue
          continue;
        }

        // Plan has no symbol keys and we use getOwnPropertyNames()
        // so `prop` cannot only be a string, not a symbol. We coerce it in place
        // with `String(..)` anyway just as good hygiene, since these paths are just
        // for diagnostic purposes.
        const subPath = `${path}.${String(prop)}`;
        const subPlan = plan[prop];

        if (subPlan === true) {
          enableProperty(subPath, obj, prop);
        } else if (subPlan === '*') {
          enableAllProperties(subPath, desc.value);
        } else if (isObject(subPlan)) {
          enableProperties(subPath, desc.value, subPlan);
        } else {
          throw new TypeError(`Unexpected override enablement plan ${subPath}`);
        }
      }
    }

    let plan;
    switch (overrideTaming) {
      case 'min': {
        plan = minEnablements;
        break;
      }
      case 'moderate': {
        plan = moderateEnablements;
        break;
      }
      default: {
        throw new Error(`unrecognized overrideTaming ${overrideTaming}`);
      }
    }

    // Do the repair.
    enableProperties('root', intrinsics, plan);
  }

  // @ts-check

  /**
   * Prepend the correct indefinite article onto a noun, typically a typeof
   * result, e.g., "an object" vs. "a number"
   *
   * @param {string} str The noun to prepend
   * @returns {string} The noun prepended with a/an
   */
  const an = str => {
    str = `${str}`;
    if (str.length >= 1 && 'aeiouAEIOU'.includes(str[0])) {
      return `an ${str}`;
    }
    return `a ${str}`;
  };
  freeze(an);

  /**
   * Like `JSON.stringify` but does not blow up if given a cycle or a bigint.
   * This is not
   * intended to be a serialization to support any useful unserialization,
   * or any programmatic use of the resulting string. The string is intended
   * *only* for showing a human under benign conditions, in order to be
   * informative enough for some
   * logging purposes. As such, this `bestEffortStringify` has an
   * imprecise specification and may change over time.
   *
   * The current `bestEffortStringify` possibly emits too many "seen"
   * markings: Not only for cycles, but also for repeated subtrees by
   * object identity.
   *
   * As a best effort only for diagnostic interpretation by humans,
   * `bestEffortStringify` also turns various cases that normal
   * `JSON.stringify` skips or errors on, like `undefined` or bigints,
   * into strings that convey their meaning. To distinguish this from
   * strings in the input, these synthesized strings always begin and
   * end with square brackets. To distinguish those strings from an
   * input string with square brackets, and input string that starts
   * with an open square bracket `[` is itself placed in square brackets.
   *
   * @param {any} payload
   * @param {(string|number)=} spaces
   * @returns {string}
   */
  const bestEffortStringify = (payload, spaces = undefined) => {
    const seenSet = new Set();
    const replacer = (_, val) => {
      switch (typeof val) {
        case 'object': {
          if (val === null) {
            return null;
          }
          if (seenSet.has(val)) {
            return '[Seen]';
          }
          seenSet.add(val);
          if (val instanceof Error) {
            return `[${val.name}: ${val.message}]`;
          }
          if (Symbol.toStringTag in val) {
            // For the built-ins that have or inherit a `Symbol.toStringTag`-named
            // property, most of them inherit the default `toString` method,
            // which will print in a similar manner: `"[object Foo]"` vs
            // `"[Foo]"`. The exceptions are
            //    * `Symbol.prototype`, `BigInt.prototype`, `String.prototype`
            //      which don't matter to us since we handle primitives
            //      separately and we don't care about primitive wrapper objects.
            //    * TODO
            //      `Date.prototype`, `TypedArray.prototype`.
            //      Hmmm, we probably should make special cases for these. We're
            //      not using these yet, so it's not urgent. But others will run
            //      into these.
            //
            // Once #2018 is closed, the only objects in our code that have or
            // inherit a `Symbol.toStringTag`-named property are remotables
            // or their remote presences.
            // This printing will do a good job for these without
            // violating abstraction layering. This behavior makes sense
            // purely in terms of JavaScript concepts. That's some of the
            // motivation for choosing that representation of remotables
            // and their remote presences in the first place.
            return `[${val[Symbol.toStringTag]}]`;
          }
          return val;
        }
        case 'function': {
          return `[Function ${val.name || '<anon>'}]`;
        }
        case 'string': {
          if (val.startsWith('[')) {
            return `[${val}]`;
          }
          return val;
        }
        case 'undefined':
        case 'symbol': {
          return `[${String(val)}]`;
        }
        case 'bigint': {
          return `[${val}n]`;
        }
        case 'number': {
          if (Object.is(val, NaN)) {
            return '[NaN]';
          } else if (val === Infinity) {
            return '[Infinity]';
          } else if (val === -Infinity) {
            return '[-Infinity]';
          }
          return val;
        }
        default: {
          return val;
        }
      }
    };
    return JSON.stringify(payload, replacer, spaces);
  };
  freeze(bestEffortStringify);

  // Copyright (C) 2019 Agoric, under Apache License 2.0

  // For our internal debugging purposes, uncomment
  // const internalDebugConsole = console;

  // /////////////////////////////////////////////////////////////////////////////

  /** @type {WeakMap<StringablePayload, any>} */
  const declassifiers = new WeakMap();

  /** @type {AssertQuote} */
  const quote = (payload, spaces = undefined) => {
    const result = freeze({
      toString: freeze(() => bestEffortStringify(payload, spaces)),
    });
    declassifiers.set(result, payload);
    return result;
  };
  freeze(quote);

  // /////////////////////////////////////////////////////////////////////////////

  /**
   * @typedef {Object} HiddenDetails
   *
   * Captures the arguments passed to the `details` template string tag.
   *
   * @property {TemplateStringsArray | string[]} template
   * @property {any[]} args
   */

  /**
   * @type {WeakMap<DetailsToken, HiddenDetails>}
   *
   * Maps from a details token which a `details` template literal returned
   * to a record of the contents of that template literal expression.
   */
  const hiddenDetailsMap = new WeakMap();

  /** @type {DetailsTag} */
  const details = (template, ...args) => {
    // Keep in mind that the vast majority of calls to `details` creates
    // a details token that is never used, so this path must remain as fast as
    // possible. Hence we store what we've got with little processing, postponing
    // all the work to happen only if needed, for example, if an assertion fails.
    const detailsToken = freeze({ __proto__: null });
    hiddenDetailsMap.set(detailsToken, { template, args });
    return detailsToken;
  };
  freeze(details);

  /**
   * @param {HiddenDetails} hiddenDetails
   * @returns {string}
   */
  const getMessageString = ({ template, args }) => {
    const parts = [template[0]];
    for (let i = 0; i < args.length; i += 1) {
      const arg = args[i];
      let argStr;
      if (declassifiers.has(arg)) {
        argStr = `${arg}`;
      } else if (arg instanceof Error) {
        argStr = `(${an(arg.name)})`;
      } else {
        argStr = `(${an(typeof arg)})`;
      }
      parts.push(argStr, template[i + 1]);
    }
    return parts.join('');
  };

  /**
   * @param {HiddenDetails} hiddenDetails
   * @returns {LogArgs}
   */
  const getLogArgs = ({ template, args }) => {
    const logArgs = [template[0]];
    for (let i = 0; i < args.length; i += 1) {
      let arg = args[i];
      if (declassifiers.has(arg)) {
        arg = declassifiers.get(arg);
      }
      // Remove the extra spaces (since console.error puts them
      // between each cause).
      const priorWithoutSpace = (logArgs.pop() || '').replace(/ $/, '');
      if (priorWithoutSpace !== '') {
        logArgs.push(priorWithoutSpace);
      }
      const nextWithoutSpace = template[i + 1].replace(/^ /, '');
      logArgs.push(arg, nextWithoutSpace);
    }
    if (logArgs[logArgs.length - 1] === '') {
      logArgs.pop();
    }
    return logArgs;
  };

  /**
   * @type {WeakMap<Error, LogArgs>}
   *
   * Maps from an error object to the log args that are a more informative
   * alternative message for that error. When logging the error, these
   * log args should be preferred to `error.message`.
   */
  const hiddenMessageLogArgs = new WeakMap();

  /**
   * @type {AssertMakeError}
   */
  const makeError = (
    optDetails = details`Assert failed`,
    ErrorConstructor = Error,
  ) => {
    if (typeof optDetails === 'string') {
      // If it is a string, use it as the literal part of the template so
      // it doesn't get quoted.
      optDetails = details([optDetails]);
    }
    const hiddenDetails = hiddenDetailsMap.get(optDetails);
    if (hiddenDetails === undefined) {
      throw new Error(`unrecognized details ${optDetails}`);
    }
    const messageString = getMessageString(hiddenDetails);
    const error = new ErrorConstructor(messageString);
    hiddenMessageLogArgs.set(error, getLogArgs(hiddenDetails));
    // The next line is a particularly fruitful place to put a breakpoint.
    return error;
  };
  freeze(makeError);

  // /////////////////////////////////////////////////////////////////////////////

  /**
   * @type {WeakMap<Error, LogArgs[]>}
   *
   * Maps from an error to an array of log args, where each log args is
   * remembered as an annotation on that error. This can be used, for example,
   * to keep track of additional causes of the error. The elements of any
   * log args may include errors which are associated with further annotations.
   * An augmented console, like the causal console of `console.js`, could
   * then retrieve the graph of such annotations.
   */
  const hiddenNoteLogArgsArrays = new WeakMap();

  /**
   * @type {WeakMap<Error, NoteCallback[]>}
   *
   * An augmented console will normally only take the hidden noteArgs array once,
   * when it logs the error being annotated. Once that happens, further
   * annotations of that error should go to the console immediately. We arrange
   * that by accepting a note-callback function from the console as an optional
   * part of that taking operation. Normally there will only be at most one
   * callback per error, but that depends on console behavior which we should not
   * assume. We make this an array of callbacks so multiple registrations
   * are independent.
   */
  const hiddenNoteCallbackArrays = new WeakMap();

  /** @type {AssertNote} */
  const note = (error, detailsNote) => {
    if (typeof detailsNote === 'string') {
      // If it is a string, use it as the literal part of the template so
      // it doesn't get quoted.
      detailsNote = details([detailsNote]);
    }
    const hiddenDetails = hiddenDetailsMap.get(detailsNote);
    if (hiddenDetails === undefined) {
      throw new Error(`unrecognized details ${detailsNote}`);
    }
    const logArgs = getLogArgs(hiddenDetails);
    const callbacks = hiddenNoteCallbackArrays.get(error);
    if (callbacks !== undefined) {
      for (const callback of callbacks) {
        callback(error, logArgs);
      }
    } else {
      const logArgsArray = hiddenNoteLogArgsArrays.get(error);
      if (logArgsArray !== undefined) {
        logArgsArray.push(logArgs);
      } else {
        hiddenNoteLogArgsArrays.set(error, [logArgs]);
      }
    }
  };
  freeze(note);

  /**
   * The unprivileged form that just uses the de facto `error.stack` property.
   * The start compartment normally has a privileged `globalThis.getStackString`
   * which should be preferred if present.
   *
   * @param {Error} error
   * @returns {string}
   */
  const defaultGetStackString = error => {
    if (!('stack' in error)) {
      return '';
    }
    const stackString = `${error.stack}`;
    const pos = stackString.indexOf('\n');
    if (stackString.startsWith(' ') || pos === -1) {
      return stackString;
    }
    return stackString.slice(pos + 1); // exclude the initial newline
  };

  /** @type {LoggedErrorHandler} */
  const loggedErrorHandler = {
    getStackString: globalThis.getStackString || defaultGetStackString,
    takeMessageLogArgs: error => {
      const result = hiddenMessageLogArgs.get(error);
      hiddenMessageLogArgs.delete(error);
      return result;
    },
    takeNoteLogArgsArray: (error, callback) => {
      const result = hiddenNoteLogArgsArrays.get(error);
      hiddenNoteLogArgsArrays.delete(error);
      if (callback !== undefined) {
        const callbacks = hiddenNoteCallbackArrays.get(error);
        if (callbacks) {
          callbacks.push(callback);
        } else {
          hiddenNoteCallbackArrays.set(error, [callback]);
        }
      }
      return result || [];
    },
  };
  freeze(loggedErrorHandler);

  // /////////////////////////////////////////////////////////////////////////////

  /**
   * @type {MakeAssert}
   */
  const makeAssert = (optRaise = undefined) => {
    /** @type {AssertFail} */
    const fail = (
      optDetails = details`Assert failed`,
      ErrorConstructor = Error,
    ) => {
      const reason = makeError(optDetails, ErrorConstructor);
      if (optRaise !== undefined) {
        optRaise(reason);
      }
      throw reason;
    };
    freeze(fail);

    // Don't freeze or export `baseAssert` until we add methods.
    // TODO If I change this from a `function` function to an arrow
    // function, I seem to get type errors from TypeScript. Why?
    /** @type {BaseAssert} */
    function baseAssert(
      flag,
      optDetails = details`Check failed`,
      ErrorConstructor = Error,
    ) {
      if (!flag) {
        throw fail(optDetails, ErrorConstructor);
      }
    }

    /** @type {AssertEqual} */
    const equal = (
      actual,
      expected,
      optDetails = details`Expected ${actual} is same as ${expected}`,
      ErrorConstructor = RangeError,
    ) => {
      baseAssert(is(actual, expected), optDetails, ErrorConstructor);
    };
    freeze(equal);

    /** @type {AssertTypeof} */
    const assertTypeof = (specimen, typename, optDetails) => {
      baseAssert(
        typeof typename === 'string',
        details`${quote(typename)} must be a string`,
      );
      if (optDetails === undefined) {
        // Like
        // ```js
        // optDetails = details`${specimen} must be ${quote(an(typename))}`;
        // ```
        // except it puts the typename into the literal part of the template
        // so it doesn't get quoted.
        optDetails = details(['', ` must be ${an(typename)}`], specimen);
      }
      equal(typeof specimen, typename, optDetails, TypeError);
    };
    freeze(assertTypeof);

    /** @type {AssertString} */
    const assertString = (specimen, optDetails) =>
      assertTypeof(specimen, 'string', optDetails);

    // Note that "assert === baseAssert"
    /** @type {Assert} */
    const assert = assign(baseAssert, {
      error: makeError,
      fail,
      equal,
      typeof: assertTypeof,
      string: assertString,
      note,
      details,
      quote,
      makeAssert,
    });
    return freeze(assert);
  };
  freeze(makeAssert);

  /** @type {Assert} */
  const assert = makeAssert();

  const { details: d, quote: q } = assert;

  const localePattern = /^(\w*[a-z])Locale([A-Z]\w*)$/;

  // Use concise methods to obtain named functions without constructor
  // behavior or `.prototype` property.
  const tamedMethods = {
    // See https://tc39.es/ecma262/#sec-string.prototype.localecompare
    localeCompare(that) {
      if (this === null || this === undefined) {
        throw new TypeError(
          'Cannot localeCompare with null or undefined "this" value',
        );
      }
      const s = `${this}`;
      that = `${that}`;
      if (s < that) {
        return -1;
      }
      if (s > that) {
        return 1;
      }
      assert(s === that, d`expected ${q(s)} and ${q(that)} to compare`);
      return 0;
    },
  };

  const nonLocaleCompare = tamedMethods.localeCompare;

  function tameLocaleMethods(intrinsics, localeTaming = 'safe') {
    if (localeTaming !== 'safe' && localeTaming !== 'unsafe') {
      throw new Error(`unrecognized dateTaming ${localeTaming}`);
    }
    if (localeTaming === 'unsafe') {
      return;
    }

    defineProperty(String.prototype, 'localeCompare', {
      value: nonLocaleCompare,
    });

    for (const intrinsicName of getOwnPropertyNames(intrinsics)) {
      const intrinsic = intrinsics[intrinsicName];
      if (intrinsic === Object(intrinsic)) {
        for (const methodName of getOwnPropertyNames(intrinsic)) {
          const match = localePattern.exec(methodName);
          if (match) {
            assert(
              typeof intrinsic[methodName] === 'function',
              d`expected ${q(methodName)} to be a function`,
            );
            const nonLocaleMethodName = `${match[1]}${match[2]}`;
            const method = intrinsic[nonLocaleMethodName];
            assert(
              typeof method === 'function',
              d`function ${q(nonLocaleMethodName)} not found`,
            );
            defineProperty(intrinsic, methodName, { value: method });
          }
        }
      }
    }
  }

  /**
   * keywords
   * In JavaScript you cannot use these reserved words as variables.
   * See 11.6.1 Identifier Names
   */
  const keywords = [
    // 11.6.2.1 Keywords
    'await',
    'break',
    'case',
    'catch',
    'class',
    'const',
    'continue',
    'debugger',
    'default',
    'delete',
    'do',
    'else',
    'export',
    'extends',
    'finally',
    'for',
    'function',
    'if',
    'import',
    'in',
    'instanceof',
    'new',
    'return',
    'super',
    'switch',
    'this',
    'throw',
    'try',
    'typeof',
    'var',
    'void',
    'while',
    'with',
    'yield',

    // Also reserved when parsing strict mode code
    'let',
    'static',

    // 11.6.2.2 Future Reserved Words
    'enum',

    // Also reserved when parsing strict mode code
    'implements',
    'package',
    'protected',
    'interface',
    'private',
    'public',

    // Reserved but not mentioned in specs
    'await',

    'null',
    'true',
    'false',

    'this',
    'arguments',
  ];

  /**
   * identifierPattern
   * Simplified validation of indentifier names: may only contain alphanumeric
   * characters (or "$" or "_"), and may not start with a digit. This is safe
   * and does not reduces the compatibility of the shim. The motivation for
   * this limitation was to decrease the complexity of the implementation,
   * and to maintain a resonable level of performance.
   * Note: \w is equivalent [a-zA-Z_0-9]
   * See 11.6.1 Identifier Names
   */
  const identifierPattern = new RegExp('^[a-zA-Z_$][\\w$]*$');

  /**
   * isValidIdentifierName()
   * What variable names might it bring into scope? These include all
   * property names which can be variable names, including the names
   * of inherited properties. It excludes symbols and names which are
   * keywords. We drop symbols safely. Currently, this shim refuses
   * service if any of the names are keywords or keyword-like. This is
   * safe and only prevent performance optimization.
   *
   * @param {string} name
   */
  function isValidIdentifierName(name) {
    // Ensure we have a valid identifier. We use regexpTest rather than
    // /../.test() to guard against the case where RegExp has been poisoned.
    return (
      name !== 'eval' &&
      !arrayIncludes(keywords, name) &&
      regexpTest(identifierPattern, name)
    );
  }

  /*
   * isImmutableDataProperty
   */

  function isImmutableDataProperty(obj, name) {
    const desc = getOwnPropertyDescriptor(obj, name);
    return (
      //
      // The getters will not have .writable, don't let the falsyness of
      // 'undefined' trick us: test with === false, not ! . However descriptors
      // inherit from the (potentially poisoned) global object, so we might see
      // extra properties which weren't really there. Accessor properties have
      // 'get/set/enumerable/configurable', while data properties have
      // 'value/writable/enumerable/configurable'.
      desc.configurable === false &&
      desc.writable === false &&
      //
      // Checks for data properties because they're the only ones we can
      // optimize (accessors are most likely non-constant). Descriptors can't
      // can't have accessors and value properties at the same time, therefore
      // this check is sufficient. Using explicit own property deal with the
      // case where Object.prototype has been poisoned.
      objectHasOwnProperty(desc, 'value')
    );
  }

  /**
   * getScopeConstants()
   * What variable names might it bring into scope? These include all
   * property names which can be variable names, including the names
   * of inherited properties. It excludes symbols and names which are
   * keywords. We drop symbols safely. Currently, this shim refuses
   * service if any of the names are keywords or keyword-like. This is
   * safe and only prevent performance optimization.
   *
   * @param {Object} globalObject
   * @param {Object} localObject
   */
  function getScopeConstants(globalObject, localObject = {}) {
    // getOwnPropertyNames() does ignore Symbols so we don't need to
    // filter them out.
    const globalNames = getOwnPropertyNames(globalObject);
    const localNames = getOwnPropertyNames(localObject);

    // Collect all valid & immutable identifiers from the endowments.
    const localConstants = localNames.filter(
      name =>
        isValidIdentifierName(name) && isImmutableDataProperty(localObject, name),
    );

    // Collect all valid & immutable identifiers from the global that
    // are also not present in the endwoments (immutable or not).
    const globalConstants = globalNames.filter(
      name =>
        // Can't define a constant: it would prevent a
        // lookup on the endowments.
        !localNames.includes(name) &&
        isValidIdentifierName(name) &&
        isImmutableDataProperty(globalObject, name),
    );

    return [...globalConstants, ...localConstants];
  }

  const { details: d$1, quote: q$1 } = assert;

  // The original unsafe untamed eval function, which must not escape.
  // Sample at module initialization time, which is before lockdown can
  // repair it.  Use it only to build powerless abstractions.
  // eslint-disable-next-line no-eval
  const FERAL_EVAL = eval;

  /**
   * alwaysThrowHandler
   * This is an object that throws if any propery is called. It's used as
   * a proxy handler which throws on any trap called.
   * It's made from a proxy with a get trap that throws. It's safe to
   * create one and share it between all scopeHandlers.
   */
  const alwaysThrowHandler = new Proxy(immutableObject, {
    get(_shadow, prop) {
      assert.fail(
        d$1`Please report unexpected scope handler trap: ${q$1(String(prop))}`,
      );
    },
  });

  /*
   * createScopeHandler()
   * ScopeHandler manages a Proxy which serves as the global scope for the
   * performEval operation (the Proxy is the argument of a 'with' binding).
   * As described in createSafeEvaluator(), it has several functions:
   * - allow the very first (and only the very first) use of 'eval' to map to
   * the real (unsafe) eval function, so it acts as a 'direct eval' and can
   * access its lexical scope (which maps to the 'with' binding, which the
   * ScopeHandler also controls).
   * - ensure that all subsequent uses of 'eval' map to the safeEvaluator,
   * which lives as the 'eval' property of the safeGlobal.
   * - route all other property lookups at the safeGlobal.
   * - hide the unsafeGlobal which lives on the scope chain above the 'with'.
   * - ensure the Proxy invariants despite some global properties being frozen.
   */
  function createScopeHandler(
    globalObject,
    localObject = {},
    { sloppyGlobalsMode = false } = {},
  ) {
    return {
      // The scope handler throws if any trap other than get/set/has are run
      // (e.g. getOwnPropertyDescriptors, apply, getPrototypeOf).
      __proto__: alwaysThrowHandler,

      // This flag allow us to determine if the eval() call is an done by the
      // realm's code or if it is user-land invocation, so we can react differently.
      useUnsafeEvaluator: false,

      get(_shadow, prop) {
        if (typeof prop === 'symbol') {
          return undefined;
        }

        // Special treatment for eval. The very first lookup of 'eval' gets the
        // unsafe (real direct) eval, so it will get the lexical scope that uses
        // the 'with' context.
        if (prop === 'eval') {
          // test that it is true rather than merely truthy
          if (this.useUnsafeEvaluator === true) {
            // revoke before use
            this.useUnsafeEvaluator = false;
            return FERAL_EVAL;
          }
          // fall through
        }

        // Properties of the localObject.
        if (prop in localObject) {
          // Use reflect to defeat accessors that could be present on the
          // localObject object itself as `this`.
          // This is done out of an overabundance of caution, as the SES shim
          // only use the localObject carry globalLexicals and live binding
          // traps.
          // The globalLexicals are captured as a snapshot of what's passed to
          // the Compartment constructor, wherein all accessors and setters are
          // eliminated and the result frozen.
          // The live binding traps do use accessors, and none of those accessors
          // make use of their receiver.
          // Live binding traps provide no avenue for user code to observe the
          // receiver.
          return reflectGet(localObject, prop, globalObject);
        }

        // Properties of the global.
        return reflectGet(globalObject, prop);
      },

      set(_shadow, prop, value) {
        // Properties of the localObject.
        if (prop in localObject) {
          const desc = getOwnPropertyDescriptor(localObject, prop);
          if ('value' in desc) {
            // Work around a peculiar behavior in the specs, where
            // value properties are defined on the receiver.
            return reflectSet(localObject, prop, value);
          }
          // Ensure that the 'this' value on setters resolves
          // to the safeGlobal, not to the localObject object.
          return reflectSet(localObject, prop, value, globalObject);
        }

        // Properties of the global.
        return reflectSet(globalObject, prop, value);
      },

      // we need has() to return false for some names to prevent the lookup from
      // climbing the scope chain and eventually reaching the unsafeGlobal
      // object (globalThis), which is bad.

      // todo: we'd like to just have has() return true for everything, and then
      // use get() to raise a ReferenceError for anything not on the safe global.
      // But we want to be compatible with ReferenceError in the normal case and
      // the lack of ReferenceError in the 'typeof' case. Must either reliably
      // distinguish these two cases (the trap behavior might be different), or
      // we rely on a mandatory source-to-source transform to change 'typeof abc'
      // to XXX. We already need a mandatory parse to prevent the 'import',
      // since it's a special form instead of merely being a global variable/

      // note: if we make has() return true always, then we must implement a
      // set() trap to avoid subverting the protection of strict mode (it would
      // accept assignments to undefined globals, when it ought to throw
      // ReferenceError for such assignments)

      has(_shadow, prop) {
        // unsafeGlobal: hide all properties of the current global
        // at the expense of 'typeof' being wrong for those properties. For
        // example, in the browser, evaluating 'document = 3', will add
        // a property to globalObject instead of throwing a ReferenceError.
        if (
          sloppyGlobalsMode ||
          prop === 'eval' ||
          prop in localObject ||
          prop in globalObject ||
          prop in globalThis
        ) {
          return true;
        }

        return false;
      },

      // note: this is likely a bug of safari
      // https://bugs.webkit.org/show_bug.cgi?id=195534

      getPrototypeOf() {
        return null;
      },

      // Chip has seen this happen single stepping under the Chrome/v8 debugger.
      // TODO record how to reliably reproduce, and to test if this fix helps.
      // TODO report as bug to v8 or Chrome, and record issue link here.

      getOwnPropertyDescriptor(_target, prop) {
        // Coerce with `String` in case prop is a symbol.
        const quotedProp = JSON.stringify(String(prop));
        console.warn(
          `getOwnPropertyDescriptor trap on scopeHandler for ${quotedProp}`,
          new Error().stack,
        );
        return undefined;
      },
    };
  }

  // Captures a key and value of the form #key=value or @key=value
  const sourceMetaEntryRegExp =
    '\\s*[@#]\\s*([a-zA-Z][a-zA-Z0-9]*)\\s*=\\s*([^\\s\\*]*)';
  // Captures either a one-line or multi-line comment containing
  // one #key=value or @key=value.
  // Produces two pairs of capture groups, but the initial two may be undefined.
  // On account of the mechanics of regular expressions, scanning from the end
  // does not allow us to capture every pair, so getSourceURL must capture and
  // trim until there are no matching comments.
  const sourceMetaEntriesRegExp = new RegExp(
    `(?:\\s*//${sourceMetaEntryRegExp}|/\\*${sourceMetaEntryRegExp}\\s*\\*/)\\s*$`,
  );

  function getSourceURL(src) {
    let sourceURL = '<unknown>';

    // Our regular expression matches the last one or two comments with key value
    // pairs at the end of the source, avoiding a scan over the entire length of
    // the string, but at the expense of being able to capture all the (key,
    // value) pair meta comments at the end of the source, which may include
    // sourceMapURL in addition to sourceURL.
    // So, we sublimate the comments out of the source until no source or no
    // comments remain.
    while (src.length > 0) {
      const match = sourceMetaEntriesRegExp.exec(src);
      if (match === null) {
        break;
      }
      src = src.slice(0, src.length - match[0].length);

      // We skip $0 since it contains the entire match.
      // The match contains four capture groups,
      // two (key, value) pairs, the first of which
      // may be undefined.
      // On the off-chance someone put two sourceURL comments in their code with
      // different commenting conventions, the latter has precedence.
      if (match[3] === 'sourceURL') {
        sourceURL = match[4];
      } else if (match[1] === 'sourceURL') {
        sourceURL = match[2];
      }
    }

    return sourceURL;
  }

  // @ts-check

  /**
   * Find the first occurence of the given pattern and return
   * the location as the approximate line number.
   *
   * @param {string} src
   * @param {RegExp} pattern
   * @returns {number}
   */
  function getLineNumber(src, pattern) {
    const index = stringSearch(src, pattern);
    if (index < 0) {
      return -1;
    }
    return stringSplit(stringSlice(src, 0, index), '\n').length;
  }

  // /////////////////////////////////////////////////////////////////////////////

  const htmlCommentPattern = new RegExp(`(?:${'<'}!--|--${'>'})`, 'g');

  /**
   * Conservatively reject the source text if it may contain text that some
   * JavaScript parsers may treat as an html-like comment. To reject without
   * parsing, `rejectHtmlComments` will also reject some other text as well.
   *
   * https://www.ecma-international.org/ecma-262/9.0/index.html#sec-html-like-comments
   * explains that JavaScript parsers may or may not recognize html
   * comment tokens "<" immediately followed by "!--" and "--"
   * immediately followed by ">" in non-module source text, and treat
   * them as a kind of line comment. Since otherwise both of these can
   * appear in normal JavaScript source code as a sequence of operators,
   * we have the terrifying possibility of the same source code parsing
   * one way on one correct JavaScript implementation, and another way
   * on another.
   *
   * This shim takes the conservative strategy of just rejecting source
   * text that contains these strings anywhere. Note that this very
   * source file is written strangely to avoid mentioning these
   * character strings explicitly.
   *
   * We do not write the regexp in a straightforward way, so that an
   * apparennt html comment does not appear in this file. Thus, we avoid
   * rejection by the overly eager rejectDangerousSources.
   *
   * @param {string} src
   * @returns {string}
   */
  function rejectHtmlComments(src) {
    const lineNumber = getLineNumber(src, htmlCommentPattern);
    if (lineNumber < 0) {
      return src;
    }
    const name = getSourceURL(src);
    throw new SyntaxError(
      `Possible HTML comment rejected at ${name}:${lineNumber}. (SES_HTML_COMMENT_REJECTED)`,
    );
  }

  /**
   * An optional transform to place ahead of `rejectHtmlComments` to evade *that*
   * rejection. However, it may change the meaning of the program.
   *
   * This evasion replaces each alleged html comment with the space-separated
   * JavaScript operator sequence that it may mean, assuming that it appears
   * outside of a comment or literal string, in source code where the JS
   * parser makes no special case for html comments (like module source code).
   * In that case, this evasion preserves the meaning of the program, though it
   * does change the souce column numbers on each effected line.
   *
   * If the html comment appeared in a literal (a string literal, regexp literal,
   * or a template literal), then this evasion will change the meaning of the
   * program by changing the text of that literal.
   *
   * If the html comment appeared in a JavaScript comment, then this evasion does
   * not change the meaning of the program because it only changes the contents of
   * those comments.
   *
   * @param { string } src
   * @returns { string }
   */
  function evadeHtmlCommentTest(src) {
    const replaceFn = match => (match[0] === '<' ? '< ! --' : '-- >');
    return src.replace(htmlCommentPattern, replaceFn);
  }

  // /////////////////////////////////////////////////////////////////////////////

  const importPattern = new RegExp('\\bimport(\\s*(?:\\(|/[/*]))', 'g');

  /**
   * Conservatively reject the source text if it may contain a dynamic
   * import expression. To reject without parsing, `rejectImportExpressions` will
   * also reject some other text as well.
   *
   * The proposed dynamic import expression is the only syntax currently
   * proposed, that can appear in non-module JavaScript code, that
   * enables direct access to the outside world that cannot be
   * surpressed or intercepted without parsing and rewriting. Instead,
   * this shim conservatively rejects any source text that seems to
   * contain such an expression. To do this safely without parsing, we
   * must also reject some valid programs, i.e., those containing
   * apparent import expressions in literal strings or comments.
   *
   * The current conservative rule looks for the identifier "import"
   * followed by either an open paren or something that looks like the
   * beginning of a comment. We assume that we do not need to worry
   * about html comment syntax because that was already rejected by
   * rejectHtmlComments.
   *
   * this \s *must* match all kinds of syntax-defined whitespace. If e.g.
   * U+2028 (LINE SEPARATOR) or U+2029 (PARAGRAPH SEPARATOR) is treated as
   * whitespace by the parser, but not matched by /\s/, then this would admit
   * an attack like: import\u2028('power.js') . We're trying to distinguish
   * something like that from something like importnotreally('power.js') which
   * is perfectly safe.
   *
   * @param { string } src
   * @returns { string }
   */
  function rejectImportExpressions(src) {
    const lineNumber = getLineNumber(src, importPattern);
    if (lineNumber < 0) {
      return src;
    }
    const name = getSourceURL(src);
    throw new SyntaxError(
      `Possible import expression rejected at ${name}:${lineNumber}. (SES_IMPORT_REJECTED)`,
    );
  }

  /**
   * An optional transform to place ahead of `rejectImportExpressions` to evade
   * *that* rejection. However, it may change the meaning of the program.
   *
   * This evasion replaces each suspicious `import` identifier with `__import__`.
   * If the alleged import expression appears in a JavaScript comment, this
   * evasion will not change the meaning of the program. If it appears in a
   * literal (string literal, regexp literal, or a template literal), then this
   * evasion will change the contents of that literal. If it appears as code
   * where it would be parsed as an expression, then it might or might not change
   * the meaning of the program, depending on the binding, if any, of the lexical
   * variable `__import__`.
   *
   * Finally, if the original appears in code where it is not parsed as an
   * expression, for example `foo.import(path)`, then this evasion would rewrite
   * to `foo.__import__(path)` which has a surprisingly different meaning.
   *
   * @param { string } src
   * @returns { string }
   */
  function evadeImportExpressionTest(src) {
    const replaceFn = (_, p1) => `__import__${p1}`;
    return src.replace(importPattern, replaceFn);
  }

  // /////////////////////////////////////////////////////////////////////////////

  const someDirectEvalPattern = new RegExp('\\beval(\\s*\\()', 'g');

  /**
   * Heuristically reject some text that seems to contain a direct eval
   * expression, with both false positives and false negavives. To reject without
   * parsing, `rejectSomeDirectEvalExpressions` may will also reject some other
   * text as well. It may also accept source text that contains a direct eval
   * written oddly, such as `(eval)(src)`. This false negative is not a security
   * vulnerability. Rather it is a compat hazard because it will execute as
   * an indirect eval under the SES-shim but as a direct eval on platforms that
   * support SES directly (like XS).
   *
   * The shim cannot correctly emulate a direct eval as explained at
   * https://github.com/Agoric/realms-shim/issues/12
   * If we did not reject direct eval syntax, we would
   * accidentally evaluate these with an emulation of indirect eval. To
   * prevent future compatibility problems, in shifting from use of the
   * shim to genuine platform support for the proposal, we should
   * instead statically reject code that seems to contain a direct eval
   * expression.
   *
   * As with the dynamic import expression, to avoid a full parse, we do
   * this approximately with a regexp, that will also reject strings
   * that appear safely in comments or strings. Unlike dynamic import,
   * if we miss some, this only creates future compat problems, not
   * security problems. Thus, we are only trying to catch innocent
   * occurrences, not malicious one. In particular, `(eval)(...)` is
   * direct eval syntax that would not be caught by the following regexp.
   *
   * Exported for unit tests.
   *
   * @param { string } src
   * @returns { string }
   */
  function rejectSomeDirectEvalExpressions(src) {
    const lineNumber = getLineNumber(src, someDirectEvalPattern);
    if (lineNumber < 0) {
      return src;
    }
    const name = getSourceURL(src);
    throw new SyntaxError(
      `Possible direct eval expression rejected at ${name}:${lineNumber}. (SES_EVAL_REJECTED)`,
    );
  }

  // /////////////////////////////////////////////////////////////////////////////

  /**
   * A transform that bundles together the transforms that must unconditionally
   * happen last in order to ensure safe evaluation without parsing.
   *
   * @param {string} source
   * @returns {string}
   */
  function mandatoryTransforms(source) {
    source = rejectHtmlComments(source);
    source = rejectImportExpressions(source);
    return source;
  }

  /**
   * Starting with `source`, apply each transform to the result of the
   * previous one, returning the result of the last transformation.
   *
   * @param {string} source
   * @param {((str: string) => string)[]} transforms
   * @returns {string}
   */
  function applyTransforms(source, transforms) {
    for (const transform of transforms) {
      source = transform(source);
    }
    return source;
  }

  // The original unsafe untamed Function constructor, which must not escape.
  // Sample at module initialization time, which is before lockdown can
  // repair it. Use it only to build powerless abstractions.
  const FERAL_FUNCTION = Function;

  /**
   * buildOptimizer()
   * Given an array of indentifier, the optimizer return a `const` declaration
   * destructring `this`.
   *
   * @param {Array<string>} constants
   */
  function buildOptimizer(constants) {
    // No need to build an oprimizer when there are no constants.
    if (constants.length === 0) return '';
    // Use 'this' to avoid going through the scope proxy, which is unecessary
    // since the optimizer only needs references to the safe global.
    return `const {${arrayJoin(constants, ',')}} = this;`;
  }

  /**
   * makeEvaluateFactory()
   * The factory create 'evaluate' functions with the correct optimizer
   * inserted.
   *
   * @param {Array<string>} [constants]
   */
  function makeEvaluateFactory(constants = []) {
    const optimizer = buildOptimizer(constants);

    // Create a function in sloppy mode, so that we can use 'with'. It returns
    // a function in strict mode that evaluates the provided code using direct
    // eval, and thus in strict mode in the same scope. We must be very careful
    // to not create new names in this scope

    // 1: we use 'with' (around a Proxy) to catch all free variable names. The
    // `this` value holds the Proxy which safely wraps the safeGlobal
    // 2: 'optimizer' catches constant variable names for speed.
    // 3: The inner strict function is effectively passed two parameters:
    //    a) its arguments[0] is the source to be directly evaluated.
    //    b) its 'this' is the this binding seen by the code being
    //       directly evaluated (the globalObject).
    // 4: The outer sloppy function is passed one parameter, the scope proxy.
    //    as the `this` parameter.

    // Notes:
    // - everything in the 'optimizer' string is looked up in the proxy
    //   (including an 'arguments[0]', which points at the Proxy).
    // - keywords like 'function' which are reserved keywords, and cannot be
    //   used as a variables, so they is not part to the optimizer.
    // - when 'eval' is looked up in the proxy, and it's the first time it is
    //   looked up after useUnsafeEvaluator is turned on, the proxy returns the
    //   eval intrinsic, and flips useUnsafeEvaluator back to false. Any reference
    //   to 'eval' in that string will get the tamed evaluator.

    return FERAL_FUNCTION(`
    with (this) {
      ${optimizer}
      return function() {
        'use strict';
        return eval(arguments[0]);
      };
    }
  `);
  }

  // Portions adapted from V8 - Copyright 2016 the V8 project authors.

  const { details: d$2 } = assert;

  /**
   * performEval()
   * The low-level operation used by all evaluators:
   * eval(), Function(), Evalutator.prototype.evaluate().
   *
   * @param {string} source
   * @param {Object} globalObject
   * @param {Objeect} localObject
   * @param {Object} [options]
   * @param {Array<Transform>} [options.localTransforms]
   * @param {Array<Transform>} [options.globalTransforms]
   * @param {bool} [options.sloppyGlobalsMode]
   * @param {WeakSet} [options.knownScopeProxies]
   */
  function performEval(
    source,
    globalObject,
    localObject = {},
    {
      localTransforms = [],
      globalTransforms = [],
      sloppyGlobalsMode = false,
      knownScopeProxies = new WeakSet(),
    } = {},
  ) {
    // Execute the mandatory transforms last to ensure that any rewritten code
    // meets those mandatory requirements.
    source = applyTransforms(source, [
      ...localTransforms,
      ...globalTransforms,
      mandatoryTransforms,
    ]);

    const scopeHandler = createScopeHandler(globalObject, localObject, {
      sloppyGlobalsMode,
    });
    const scopeProxyRevocable = proxyRevocable(immutableObject, scopeHandler);
    // Ensure that "this" resolves to the scope proxy.

    const constants = getScopeConstants(globalObject, localObject);
    const evaluateFactory = makeEvaluateFactory(constants);
    const evaluate = apply(evaluateFactory, scopeProxyRevocable.proxy, []);

    scopeHandler.useUnsafeEvaluator = true;
    let err;
    try {
      // Ensure that "this" resolves to the safe global.
      knownScopeProxies.add(scopeProxyRevocable.proxy);
      return apply(evaluate, globalObject, [source]);
    } catch (e) {
      // stash the child-code error in hopes of debugging the internal failure
      err = e;
      throw e;
    } finally {
      if (scopeHandler.useUnsafeEvaluator === true) {
        // The proxy switches off useUnsafeEvaluator immediately after
        // the first access, but if that's not the case we should abort.
        // This condition is one where this vat is now hopelessly confused,
        // and the vat as a whole should be aborted. All immediately reachable
        // state should be abandoned. However, that is not yet possible,
        // so we at least prevent further variable resolution via the
        // scopeHandler, and throw an error with diagnostic info including
        // the thrown error if any from evaluating the source code.
        scopeProxyRevocable.revoke();
        // TODO A GOOD PLACE TO PANIC(), i.e., kill the vat incarnation.
        // See https://github.com/Agoric/SES-shim/issues/490
        assert.fail(d$2`handler did not revoke useUnsafeEvaluator ${err}`);
      }
    }
  }

  /*
   * makeEvalFunction()
   * A safe version of the native eval function which relies on
   * the safety of performEval for confinement.
   */
  const makeEvalFunction = (globalObject, options = {}) => {
    // We use the the concise method syntax to create an eval without a
    // [[Construct]] behavior (such that the invocation "new eval()" throws
    // TypeError: eval is not a constructor"), but which still accepts a
    // 'this' binding.
    const newEval = {
      eval(source) {
        if (typeof source !== 'string') {
          // As per the runtime semantic of PerformEval [ECMAScript 18.2.1.1]:
          // If Type(source) is not String, return source.
          // TODO Recent proposals from Mike Samuel may change this non-string
          // rule. Track.
          return source;
        }
        return performEval(source, globalObject, {}, options);
      },
    }.eval;

    return newEval;
  };

  // The original unsafe untamed Function constructor, which must not escape.
  // Sample at module initialization time, which is before lockdown can
  // repair it.  Use it only to build powerless abstractions.
  const FERAL_FUNCTION$1 = Function;

  /*
   * makeFunctionConstructor()
   * A safe version of the native Function which relies on
   * the safety of performEval for confinement.
   */
  function makeFunctionConstructor(globaObject, options = {}) {
    // Define an unused parameter to ensure Function.length === 1
    const newFunction = function Function(_body) {
      // Sanitize all parameters at the entry point.
      // eslint-disable-next-line prefer-rest-params
      const bodyText = `${arrayPop(arguments) || ''}`;
      // eslint-disable-next-line prefer-rest-params
      const parameters = `${arrayJoin(arguments, ',')}`;

      // Are parameters and bodyText valid code, or is someone
      // attempting an injection attack? This will throw a SyntaxError if:
      // - parameters doesn't parse as parameters
      // - bodyText doesn't parse as a function body
      // - either contain a call to super() or references a super property.
      // eslint-disable-next-line no-new
      new FERAL_FUNCTION$1(parameters, bodyText);

      // Safe to be combined. Defeat potential trailing comments.
      // TODO: since we create an anonymous function, the 'this' value
      // isn't bound to the global object as per specs, but set as undefined.
      const src = `(function anonymous(${parameters}\n) {\n${bodyText}\n})`;
      return performEval(src, globaObject, {}, options);
    };

    defineProperties(newFunction, {
      // Ensure that any function created in any evaluator in a realm is an
      // instance of Function in any evaluator of the same realm.
      prototype: {
        value: Function.prototype,
        writable: false,
        enumerable: false,
        configurable: false,
      },
    });

    // Assert identity of Function.__proto__ accross all compartments
    assert(
      getPrototypeOf(Function) === Function.prototype,
      'Function prototype is the same accross compartments',
    );
    assert(
      getPrototypeOf(newFunction) === Function.prototype,
      'Function constructor prototype is the same accross compartments',
    );

    return newFunction;
  }

  /**
   * initGlobalObject()
   * Create new global object using a process similar to ECMA specifications
   * (portions of SetRealmGlobalObject and SetDefaultGlobalBindings).
   * `newGlobalPropertyNames` should be either `initialGlobalPropertyNames` or
   * `sharedGlobalPropertyNames`.
   *
   * @param {Object} globalObject
   * @param {Object} intrinsics
   * @param {Object} newGlobalPropertyNames
   * @param {Function} makeCompartmentConstructor
   * @param {Object} compartmentPrototype
   * @param {Object} [options]
   * @param {Array<Transform>} [options.globalTransforms]
   * @param {(Object) => void} [options.nativeBrander]
   */
  function initGlobalObject(
    globalObject,
    intrinsics,
    newGlobalPropertyNames,
    makeCompartmentConstructor,
    compartmentPrototype,
    { globalTransforms, nativeBrander },
  ) {
    for (const [name, constant] of entries(constantProperties)) {
      defineProperty(globalObject, name, {
        value: constant,
        writable: false,
        enumerable: false,
        configurable: false,
      });
    }

    for (const [name, intrinsicName] of entries(universalPropertyNames)) {
      if (objectHasOwnProperty(intrinsics, intrinsicName)) {
        defineProperty(globalObject, name, {
          value: intrinsics[intrinsicName],
          writable: true,
          enumerable: false,
          configurable: true,
        });
      }
    }

    for (const [name, intrinsicName] of entries(newGlobalPropertyNames)) {
      if (objectHasOwnProperty(intrinsics, intrinsicName)) {
        defineProperty(globalObject, name, {
          value: intrinsics[intrinsicName],
          writable: true,
          enumerable: false,
          configurable: true,
        });
      }
    }

    const perCompartmentGlobals = {
      globalThis: globalObject,
      eval: makeEvalFunction(globalObject, {
        globalTransforms,
      }),
      Function: makeFunctionConstructor(globalObject, {
        globalTransforms,
      }),
    };

    perCompartmentGlobals.Compartment = makeCompartmentConstructor(
      makeCompartmentConstructor,
      intrinsics,
      nativeBrander,
    );

    // TODO These should still be tamed according to the whitelist before
    // being made available.
    for (const [name, value] of entries(perCompartmentGlobals)) {
      defineProperty(globalObject, name, {
        value,
        writable: true,
        enumerable: false,
        configurable: true,
      });
      if (typeof value === 'function') {
        nativeBrander(value);
      }
    }
  }

  // @ts-check

  // For our internal debugging purposes, uncomment
  // const internalDebugConsole = console;

  // The whitelists of console methods, from:
  // Whatwg "living standard" https://console.spec.whatwg.org/
  // Node https://nodejs.org/dist/latest-v14.x/docs/api/console.html
  // MDN https://developer.mozilla.org/en-US/docs/Web/API/Console_API
  // TypeScript https://openstapps.gitlab.io/projectmanagement/interfaces/_node_modules__types_node_globals_d_.console.html
  // Chrome https://developers.google.com/web/tools/chrome-devtools/console/api

  // All console level methods have parameters (fmt?, ...args)
  // where the argument sequence `fmt?, ...args` formats args according to
  // fmt if fmt is a format string. Otherwise, it just renders them all as values
  // separated by spaces.
  // https://console.spec.whatwg.org/#formatter
  // https://nodejs.org/docs/latest/api/util.html#util_util_format_format_args

  // For the causal console, all occurrences of `fmt, ...args` or `...args` by
  // itself must check for the presence of an error to ask the
  // `loggedErrorHandler` to handle.
  // In theory we should do a deep inspection to detect for example an array
  // containing an error. We currently do not detect these and may never.

  /** @typedef {keyof VirtualConsole | 'profile' | 'profileEnd'} ConsoleProps */

  /** @type {readonly [ConsoleProps, LogSeverity | undefined][]} */
  const consoleLevelMethods = freeze([
    ['debug', 'debug'], // (fmt?, ...args) verbose level on Chrome
    ['log', 'log'], // (fmt?, ...args) info level on Chrome
    ['info', 'info'], // (fmt?, ...args)
    ['warn', 'warn'], // (fmt?, ...args)
    ['error', 'error'], // (fmt?, ...args)

    ['trace', 'log'], // (fmt?, ...args)
    ['dirxml', 'log'], // (fmt?, ...args)
    ['group', 'log'], // (fmt?, ...args)
    ['groupCollapsed', 'log'], // (fmt?, ...args)
  ]);

  /** @type {readonly [ConsoleProps, LogSeverity | undefined][]} */
  const consoleOtherMethods = freeze([
    ['assert', 'error'], // (value, fmt?, ...args)
    ['timeLog', 'log'], // (label?, ...args) no fmt string

    // Insensitive to whether any argument is an error. All arguments can pass
    // thru to baseConsole as is.
    ['clear', undefined], // ()
    ['count', 'info'], // (label?)
    ['countReset', undefined], // (label?)
    ['dir', 'log'], // (item, options?)
    ['groupEnd', 'log'], // ()
    // In theory tabular data may be or contain an error. However, we currently
    // do not detect these and may never.
    ['table', 'log'], // (tabularData, properties?)
    ['time', 'info'], // (label?)
    ['timeEnd', 'info'], // (label?)

    // Node Inspector only, MDN, and TypeScript, but not whatwg
    ['profile', undefined], // (label?)
    ['profileEnd', undefined], // (label?)
    ['timeStamp', undefined], // (label?)
  ]);

  /** @type {readonly [ConsoleProps, LogSeverity | undefined][]} */
  const consoleWhitelist = freeze([
    ...consoleLevelMethods,
    ...consoleOtherMethods,
  ]);

  /**
   * consoleOmittedProperties is currently unused. I record and maintain it here
   * with the intention that it be treated like the `false` entries in the main
   * SES whitelist: that seeing these on the original console is expected, but
   * seeing anything else that's outside the whitelist is surprising and should
   * provide a diagnostic.
   *
   * const consoleOmittedProperties = freeze([
   *   'memory', // Chrome
   *   'exception', // FF, MDN
   *   '_ignoreErrors', // Node
   *   '_stderr', // Node
   *   '_stderrErrorHandler', // Node
   *   '_stdout', // Node
   *   '_stdoutErrorHandler', // Node
   *   '_times', // Node
   *   'context', // Chrome, Node
   *   'record', // Safari
   *   'recordEnd', // Safari
   *
   *   'screenshot', // Safari
   *   // Symbols
   *   '@@toStringTag', // Chrome: "Object", Safari: "Console"
   *   // A variety of other symbols also seen on Node
   * ]);
   */

  // /////////////////////////////////////////////////////////////////////////////

  /** @type {MakeLoggingConsoleKit} */
  const makeLoggingConsoleKit = () => {
    // Not frozen!
    let logArray = [];

    const loggingConsole = fromEntries(
      consoleWhitelist.map(([name, _]) => {
        // Use an arrow function so that it doesn't come with its own name in
        // its printed form. Instead, we're hoping that tooling uses only
        // the `.name` property set below.
        /**
         * @param {...any} args
         */
        const method = (...args) => {
          logArray.push([name, ...args]);
        };
        defineProperty(method, 'name', { value: name });
        return [name, freeze(method)];
      }),
    );
    freeze(loggingConsole);

    const takeLog = () => {
      const result = freeze(logArray);
      logArray = [];
      return result;
    };
    freeze(takeLog);

    const typedLoggingConsole = /** @type {VirtualConsole} */ (loggingConsole);

    return freeze({ loggingConsole: typedLoggingConsole, takeLog });
  };
  freeze(makeLoggingConsoleKit);

  // /////////////////////////////////////////////////////////////////////////////

  /** @type {ErrorInfo} */
  const ErrorInfo = {
    NOTE: 'ERROR_NOTE:',
    MESSAGE: 'ERROR_MESSAGE:',
  };
  freeze(ErrorInfo);

  /**
   * The error annotations are sent to the baseConsole by calling some level
   * method. The 'debug' level seems best, because the Chrome console classifies
   * `debug` as verbose and does not show it by default. But we keep it symbolic
   * so we can change our mind. (On Node, `debug`, `log`, and `info` are aliases
   * for the same function and so will behave the same there.)
   */
  const BASE_CONSOLE_LEVEL = 'debug';

  /** @type {MakeCausalConsole} */
  const makeCausalConsole = (baseConsole, loggedErrorHandler) => {
    const {
      getStackString,
      takeMessageLogArgs,
      takeNoteLogArgsArray,
    } = loggedErrorHandler;

    // by "tagged", we mean first sent to the baseConsole as an argument in a
    // console level method call, in which it is shown with an identifying tag
    // number. We number the errors according to the order in
    // which they were first logged to the baseConsole, starting at 1.
    let numErrorsTagged = 0;
    /** @type WeakMap<Error, number> */
    const errorTagOrder = new WeakMap();

    /**
     * @param {Error} err
     * @returns {string}
     */
    const tagError = err => {
      let errNum;
      if (errorTagOrder.has(err)) {
        errNum = errorTagOrder.get(err);
      } else {
        numErrorsTagged += 1;
        errorTagOrder.set(err, numErrorsTagged);
        errNum = numErrorsTagged;
      }
      return `${err.name}#${errNum}`;
    };

    /**
     * @param {ReadonlyArray<any>} logArgs
     * @param {Array<any>} subErrorsSink
     * @returns {any}
     */
    const extractErrorArgs = (logArgs, subErrorsSink) => {
      const argTags = logArgs.map(arg => {
        if (arg instanceof Error) {
          subErrorsSink.push(arg);
          return `(${tagError(arg)})`;
        }
        return arg;
      });
      return argTags;
    };

    /**
     * @param {Error} error
     * @param {ErrorInfoKind} kind
     * @param {readonly any[]} logArgs
     * @param {Array<Error>} subErrorsSink
     */
    const logErrorInfo = (error, kind, logArgs, subErrorsSink) => {
      const errorTag = tagError(error);
      const errorName =
        kind === ErrorInfo.MESSAGE ? `${errorTag}:` : `${errorTag} ${kind}`;
      const argTags = extractErrorArgs(logArgs, subErrorsSink);
      baseConsole[BASE_CONSOLE_LEVEL](errorName, ...argTags);
    };

    /**
     * Logs the `subErrors` within a group name mentioning `optTag`.
     *
     * @param {Error[]} subErrors
     * @param {string | undefined} optTag
     * @returns {void}
     */
    const logSubErrors = (subErrors, optTag = undefined) => {
      if (subErrors.length === 0) {
        return;
      }
      if (subErrors.length === 1 && optTag === undefined) {
        // eslint-disable-next-line no-use-before-define
        logError(subErrors[0]);
        return;
      }
      let label;
      if (subErrors.length === 1) {
        label = `Nested error`;
      } else {
        label = `Nested ${subErrors.length} errors`;
      }
      if (optTag !== undefined) {
        label = `${label} under ${optTag}`;
      }
      baseConsole.group(label);
      try {
        for (const subError of subErrors) {
          // eslint-disable-next-line no-use-before-define
          logError(subError);
        }
      } finally {
        baseConsole.groupEnd();
      }
    };

    const errorsLogged = new WeakSet();

    /** @type {NoteCallback} */
    const noteCallback = (error, noteLogArgs) => {
      const subErrors = [];
      // Annotation arrived after the error has already been logged,
      // so just log the annotation immediately, rather than remembering it.
      logErrorInfo(error, ErrorInfo.NOTE, noteLogArgs, subErrors);
      logSubErrors(subErrors, tagError(error));
    };

    /**
     * @param {Error} error
     */
    const logError = error => {
      if (errorsLogged.has(error)) {
        return;
      }
      const errorTag = tagError(error);
      errorsLogged.add(error);
      const subErrors = [];
      const messageLogArgs = takeMessageLogArgs(error);
      const noteLogArgsArray = takeNoteLogArgsArray(error, noteCallback);
      // Show the error's most informative error message
      if (messageLogArgs === undefined) {
        // If there is no message log args, then just show the message that
        // the error itself carries.
        baseConsole[BASE_CONSOLE_LEVEL](`${errorTag}:`, error.message);
      } else {
        // If there is one, we take it to be strictly more informative than the
        // message string carried by the error, so show it *instead*.
        logErrorInfo(error, ErrorInfo.MESSAGE, messageLogArgs, subErrors);
      }
      // After the message but before any other annotations, show the stack.
      let stackString = getStackString(error);
      if (
        typeof stackString === 'string' &&
        stackString.length >= 1 &&
        !stackString.endsWith('\n')
      ) {
        stackString += '\n';
      }
      baseConsole[BASE_CONSOLE_LEVEL](stackString);
      // Show the other annotations on error
      for (const noteLogArgs of noteLogArgsArray) {
        logErrorInfo(error, ErrorInfo.NOTE, noteLogArgs, subErrors);
      }
      // explain all the errors seen in the messages already emitted.
      logSubErrors(subErrors, errorTag);
    };

    const levelMethods = consoleLevelMethods.map(([level, _]) => {
      /**
       * @param {...any} logArgs
       */
      const levelMethod = (...logArgs) => {
        const subErrors = [];
        const argTags = extractErrorArgs(logArgs, subErrors);
        // @ts-ignore
        baseConsole[level](...argTags);
        logSubErrors(subErrors);
      };
      defineProperty(levelMethod, 'name', { value: level });
      return [level, freeze(levelMethod)];
    });
    const otherMethodNames = consoleOtherMethods.filter(
      ([name, _]) => name in baseConsole,
    );
    const otherMethods = otherMethodNames.map(([name, _]) => {
      /**
       * @param {...any} args
       */
      const otherMethod = (...args) => {
        // @ts-ignore
        baseConsole[name](...args);
        return undefined;
      };
      defineProperty(otherMethod, 'name', { value: name });
      return [name, freeze(otherMethod)];
    });

    const causalConsole = fromEntries([...levelMethods, ...otherMethods]);
    return freeze(causalConsole);
  };
  freeze(makeCausalConsole);

  // /////////////////////////////////////////////////////////////////////////////

  /** @type {FilterConsole} */
  const filterConsole = (baseConsole, filter, _topic = undefined) => {
    // TODO do something with optional topic string
    const whilelist = consoleWhitelist.filter(([name, _]) => name in baseConsole);
    const methods = whilelist.map(([name, severity]) => {
      /**
       * @param {...any} args
       */
      const method = (...args) => {
        if (severity === undefined || filter.canLog(severity)) {
          // @ts-ignore
          baseConsole[name](...args);
        }
      };
      return [name, freeze(method)];
    });
    const filteringConsole = fromEntries(methods);
    return freeze(filteringConsole);
  };
  freeze(filterConsole);

  // @ts-check

  const originalConsole = console;

  /**
   * Wrap console unless suppressed.
   * At the moment, the console is considered a host power in the start
   * compartment, and not a primordial. Hence it is absent from the whilelist
   * and bypasses the intrinsicsCollector.
   *
   * @param {"safe" | "unsafe"} consoleTaming
   * @param {GetStackString=} optGetStackString
   */
  const tameConsole = (
    consoleTaming = 'safe',
    optGetStackString = undefined,
  ) => {
    if (consoleTaming !== 'safe' && consoleTaming !== 'unsafe') {
      throw new Error(`unrecognized consoleTaming ${consoleTaming}`);
    }

    if (consoleTaming === 'unsafe') {
      return { console: originalConsole };
    }
    let loggedErrorHandler$1;
    if (optGetStackString === undefined) {
      loggedErrorHandler$1 = loggedErrorHandler;
    } else {
      loggedErrorHandler$1 = {
        ...loggedErrorHandler,
        getStackString: optGetStackString,
      };
    }
    const causalConsole = makeCausalConsole(originalConsole, loggedErrorHandler$1);
    return { console: causalConsole };
  };

  // Whitelist names from https://v8.dev/docs/stack-trace-api
  // Whitelisting only the names used by error-stack-shim/src/v8StackFrames
  // callSiteToFrame to shim the error stack proposal.
  const safeV8CallSiteMethodNames = [
    // suppress 'getThis' definitely
    'getTypeName',
    // suppress 'getFunction' definitely
    'getFunctionName',
    'getMethodName',
    'getFileName',
    'getLineNumber',
    'getColumnNumber',
    'getEvalOrigin',
    'isToplevel',
    'isEval',
    'isNative',
    'isConstructor',
    'isAsync',
    // suppress 'isPromiseAll' for now
    // suppress 'getPromiseIndex' for now

    // Additional names found by experiment, absent from
    // https://v8.dev/docs/stack-trace-api
    'getPosition',
    'getScriptNameOrSourceURL',

    'toString', // TODO replace to use only whitelisted info
  ];

  // TODO this is a ridiculously expensive way to attenuate callsites.
  // Before that matters, we should switch to a reasonable representation.
  const safeV8CallSiteFacet = callSite => {
    const methodEntry = name => [name, () => callSite[name]()];
    const o = fromEntries(safeV8CallSiteMethodNames.map(methodEntry));
    return Object.create(o, {});
  };

  const safeV8SST = sst => sst.map(safeV8CallSiteFacet);

  // If it has `/node_modules/` anywhere in it, on Node it is likely
  // to be a dependent package of the current package, and so to
  // be an infrastructure frame to be dropped from concise stack traces.
  const FILENAME_NODE_DEPENDENTS_CENSOR = /\/node_modules\//;

  // If it begins with `internal/` or `node:internal` then it is likely
  // part of the node infrustructre itself, to be dropped from concise
  // stack traces.
  const FILENAME_NODE_INTERNALS_CENSOR = /^(?:node:)?internal\//;

  // Frames within the `assert.js` package should be dropped from
  // concise stack traces, as these are just steps towards creating the
  // error object in question.
  const FILENAME_ASSERT_CENSOR = /\/packages\/ses\/src\/error\/assert.js$/;

  // Frames within the `eventual-send` shim should be dropped so that concise
  // deep stacks omit the internals of the eventual-sending mechanism causing
  // asynchronous messages to be sent.
  // Note that the eventual-send package will move from agoric-sdk to
  // Endo, so this rule will be of general interest.
  const FILENAME_EVENTUAL_SEND_CENSOR = /\/packages\/eventual-send\/src\//;

  // Any stack frame whose `fileName` matches any of these censor patterns
  // will be omitted from concise stacks.
  // TODO Enable users to configure FILENAME_CENSORS via `lockdown` options.
  const FILENAME_CENSORS = [
    FILENAME_NODE_DEPENDENTS_CENSOR,
    FILENAME_NODE_INTERNALS_CENSOR,
    FILENAME_ASSERT_CENSOR,
    FILENAME_EVENTUAL_SEND_CENSOR,
  ];

  // Should a stack frame with this as its fileName be included in a concise
  // stack trace?
  // Exported only so it can be unit tested.
  // TODO Move so that it applies not just to v8.
  const filterFileName = fileName => {
    if (!fileName) {
      // Stack frames with no fileName should appear in concise stack traces.
      return true;
    }
    for (const filter of FILENAME_CENSORS) {
      if (filter.test(fileName)) {
        return false;
      }
    }
    return true;
  };

  // The ad-hoc rule of the current pattern is that any likely-file-path or
  // likely url-path prefix, ending in a `/.../` should get dropped.
  // Anything to the left of the likely path text is kept.
  // Everything to the right of `/.../` is kept. Thus
  // `'Object.bar (/vat-v1/.../eventual-send/test/test-deep-send.js:13:21)'`
  // simplifies to
  // `'Object.bar (eventual-send/test/test-deep-send.js:13:21)'`.
  //
  // See thread starting at
  // https://github.com/Agoric/agoric-sdk/issues/2326#issuecomment-773020389
  const CALLSITE_ELLIPSES_PATTERN = /^((?:.*[( ])?)[:/\w_-]*\/\.\.\.\/(.+)$/;

  // The ad-hoc rule of the current pattern is that any likely-file-path or
  // likely url-path prefix, ending in a `/` and prior to `package/` should get
  // dropped.
  // Anything to the left of the likely path prefix text is kept. `package/` and
  // everything to its right is kept. Thus
  // `'Object.bar (/Users/markmiller/src/ongithub/agoric/agoric-sdk/packages/eventual-send/test/test-deep-send.js:13:21)'`
  // simplifies to
  // `'Object.bar (packages/eventual-send/test/test-deep-send.js:13:21)'`.
  // Note that `/packages/` is a convention for monorepos encouraged by
  // lerna.
  const CALLSITE_PACKAGES_PATTERN = /^((?:.*[( ])?)[:/\w_-]*\/(packages\/.+)$/;

  // The use of these callSite patterns below assumes that any match will bind
  // capture groups containing the parts of the original string we want
  // to keep. The parts outside those capture groups will be dropped from concise
  // stacks.
  // TODO Enable users to configure CALLSITE_PATTERNS via `lockdown` options.
  const CALLSITE_PATTERNS = [
    CALLSITE_ELLIPSES_PATTERN,
    CALLSITE_PACKAGES_PATTERN,
  ];

  // For a stack frame that should be included in a concise stack trace, if
  // `callSiteString` is the original stringified stack frame, return the
  // possibly-shorter stringified stack frame that should be shown instead.
  // Exported only so it can be unit tested.
  // TODO Move so that it applies not just to v8.
  const shortenCallSiteString = callSiteString => {
    for (const filter of CALLSITE_PATTERNS) {
      const match = filter.exec(callSiteString);
      if (match) {
        return match.slice(1).join('');
      }
    }
    return callSiteString;
  };

  function tameV8ErrorConstructor(
    OriginalError,
    InitialError,
    errorTaming,
    stackFiltering,
  ) {
    // const callSiteFilter = _callSite => true;
    const callSiteFilter = callSite => {
      if (stackFiltering === 'verbose') {
        return true;
      }
      return filterFileName(callSite.getFileName());
    };

    const callSiteStringifier = callSite => {
      let callSiteString = `${callSite}`;
      if (stackFiltering === 'concise') {
        callSiteString = shortenCallSiteString(callSiteString);
      }
      return `\n  at ${callSiteString}`;
    };

    const stackStringFromSST = (_error, sst) =>
      [...sst.filter(callSiteFilter).map(callSiteStringifier)].join('');

    // Mapping from error instance to the structured stack trace capturing the
    // stack for that instance.
    const ssts = new WeakMap();

    // Use concise methods to obtain named functions without constructors.
    const tamedMethods = {
      // The optional `optFn` argument is for cutting off the bottom of
      // the stack --- for capturing the stack only above the topmost
      // call to that function. Since this isn't the "real" captureStackTrace
      // but instead calls the real one, if no other cutoff is provided,
      // we cut this one off.
      captureStackTrace(error, optFn = tamedMethods.captureStackTrace) {
        if (typeof OriginalError.captureStackTrace === 'function') {
          // OriginalError.captureStackTrace is only on v8
          OriginalError.captureStackTrace(error, optFn);
          return;
        }
        Reflect.set(error, 'stack', '');
      },
      // Shim of proposed special power, to reside by default only
      // in the start compartment, for getting the stack traceback
      // string associated with an error.
      // See https://tc39.es/proposal-error-stacks/
      getStackString(error) {
        if (!ssts.has(error)) {
          // eslint-disable-next-line no-void
          void error.stack;
        }
        const sst = ssts.get(error);
        if (!sst) {
          return '';
        }
        return stackStringFromSST(error, sst);
      },
      prepareStackTrace(error, sst) {
        ssts.set(error, sst);
        if (errorTaming === 'unsafe') {
          const stackString = stackStringFromSST(error, sst);
          return `${error}${stackString}`;
        }
        return '';
      },
    };

    // A prepareFn is a prepareStackTrace function.
    // An sst is a `structuredStackTrace`, which is an array of
    // callsites.
    // A user prepareFn is a prepareFn defined by a client of this API,
    // and provided by assigning to `Error.prepareStackTrace`.
    // A user prepareFn should only receive an attenuated sst, which
    // is an array of attenuated callsites.
    // A system prepareFn is the prepareFn created by this module to
    // be installed on the real `Error` constructor, to receive
    // an original sst, i.e., an array of unattenuated callsites.
    // An input prepareFn is a function the user assigns to
    // `Error.prepareStackTrace`, which might be a user prepareFn or
    // a system prepareFn previously obtained by reading
    // `Error.prepareStackTrace`.

    const defaultPrepareFn = tamedMethods.prepareStackTrace;

    OriginalError.prepareStackTrace = defaultPrepareFn;

    // A weakset branding some functions as system prepareFns, all of which
    // must be defined by this module, since they can receive an
    // unattenuated sst.
    const systemPrepareFnSet = new WeakSet([defaultPrepareFn]);

    const systemPrepareFnFor = inputPrepareFn => {
      if (systemPrepareFnSet.has(inputPrepareFn)) {
        return inputPrepareFn;
      }
      // Use concise methods to obtain named functions without constructors.
      const systemMethods = {
        prepareStackTrace(error, sst) {
          ssts.set(error, sst);
          return inputPrepareFn(error, safeV8SST(sst));
        },
      };
      systemPrepareFnSet.add(systemMethods.prepareStackTrace);
      return systemMethods.prepareStackTrace;
    };

    // Note `stackTraceLimit` accessor already defined by
    // tame-error-constructor.js
    defineProperties(InitialError, {
      captureStackTrace: {
        value: tamedMethods.captureStackTrace,
        writable: true,
        enumerable: false,
        configurable: true,
      },
      prepareStackTrace: {
        get() {
          return OriginalError.prepareStackTrace;
        },
        set(inputPrepareStackTraceFn) {
          if (typeof inputPrepareStackTraceFn === 'function') {
            const systemPrepareFn = systemPrepareFnFor(inputPrepareStackTraceFn);
            OriginalError.prepareStackTrace = systemPrepareFn;
          } else {
            OriginalError.prepareStackTrace = defaultPrepareFn;
          }
        },
        enumerable: false,
        configurable: true,
      },
    });

    return tamedMethods.getStackString;
  }

  // Present on at least FF. Proposed by Error-proposal. Not on SES whitelist
  // so grab it before it is removed.
  const stackDesc = getOwnPropertyDescriptor(Error.prototype, 'stack');
  const stackGetter = stackDesc && stackDesc.get;

  // Use concise methods to obtain named functions without constructors.
  const tamedMethods$1 = {
    getStackString(error) {
      if (typeof stackGetter === 'function') {
        return apply(stackGetter, error, []);
      } else if ('stack' in error) {
        // The fallback is to just use the de facto `error.stack` if present
        return `${error.stack}`;
      }
      return '';
    },
  };

  function tameErrorConstructor(
    errorTaming = 'safe',
    stackFiltering = 'concise',
  ) {
    if (errorTaming !== 'safe' && errorTaming !== 'unsafe') {
      throw new Error(`unrecognized errorTaming ${errorTaming}`);
    }
    if (stackFiltering !== 'concise' && stackFiltering !== 'verbose') {
      throw new Error(`unrecognized stackFiltering ${stackFiltering}`);
    }
    const OriginalError = Error;
    const ErrorPrototype = OriginalError.prototype;

    const platform =
      typeof OriginalError.captureStackTrace === 'function' ? 'v8' : 'unknown';

    const makeErrorConstructor = (_ = {}) => {
      const ResultError = function Error(...rest) {
        let error;
        if (new.target === undefined) {
          error = apply(OriginalError, this, rest);
        } else {
          error = construct(OriginalError, rest, new.target);
        }
        if (platform === 'v8') {
          // TODO Likely expensive!
          OriginalError.captureStackTrace(error, ResultError);
        }
        return error;
      };
      defineProperties(ResultError, {
        length: { value: 1 },
        prototype: {
          value: ErrorPrototype,
          writable: false,
          enumerable: false,
          configurable: false,
        },
      });
      return ResultError;
    };
    const InitialError = makeErrorConstructor({ powers: 'original' });
    const SharedError = makeErrorConstructor({ powers: 'none' });
    defineProperties(ErrorPrototype, {
      constructor: { value: SharedError },
      /* TODO
      stack: {
        get() {
          return '';
        },
        set(_) {
          // ignore
        },
      },
      */
    });

    for (const NativeError of NativeErrors) {
      setPrototypeOf(NativeError, SharedError);
    }

    // https://v8.dev/docs/stack-trace-api#compatibility advises that
    // programmers can "always" set `Error.stackTraceLimit`
    // even on non-v8 platforms. On non-v8
    // it will have no effect, but this advice only makes sense
    // if the assignment itself does not fail, which it would
    // if `Error` were naively frozen. Hence, we add setters that
    // accept but ignore the assignment on non-v8 platforms.
    defineProperties(InitialError, {
      stackTraceLimit: {
        get() {
          if (typeof OriginalError.stackTraceLimit === 'number') {
            // OriginalError.stackTraceLimit is only on v8
            return OriginalError.stackTraceLimit;
          }
          return undefined;
        },
        set(newLimit) {
          if (typeof newLimit !== 'number') {
            // silently do nothing. This behavior doesn't precisely
            // emulate v8 edge-case behavior. But given the purpose
            // of this emulation, having edge cases err towards
            // harmless seems the safer option.
            return;
          }
          if (typeof OriginalError.stackTraceLimit === 'number') {
            // OriginalError.stackTraceLimit is only on v8
            OriginalError.stackTraceLimit = newLimit;
            // We place the useless return on the next line to ensure
            // that anything we place after the if in the future only
            // happens if the then-case does not.
            // eslint-disable-next-line no-useless-return
            return;
          }
        },
        // WTF on v8 stackTraceLimit is enumerable
        enumerable: false,
        configurable: true,
      },
    });

    // The default SharedError much be completely powerless even on v8,
    // so the lenient `stackTraceLimit` accessor does nothing on all
    // platforms.
    defineProperties(SharedError, {
      stackTraceLimit: {
        get() {
          return undefined;
        },
        set(_newLimit) {
          // do nothing
        },
        enumerable: false,
        configurable: true,
      },
    });

    let initialGetStackString = tamedMethods$1.getStackString;
    if (platform === 'v8') {
      initialGetStackString = tameV8ErrorConstructor(
        OriginalError,
        InitialError,
        errorTaming,
        stackFiltering,
      );
    }
    return {
      '%InitialGetStackString%': initialGetStackString,
      '%InitialError%': InitialError,
      '%SharedError%': SharedError,
    };
  }

  // Copyright (C) 2018 Agoric

  /**
   * @typedef {{
   *   dateTaming?: 'safe' | 'unsafe',
   *   errorTaming?: 'safe' | 'unsafe',
   *   mathTaming?: 'safe' | 'unsafe',
   *   regExpTaming?: 'safe' | 'unsafe',
   *   localeTaming?: 'safe' | 'unsafe',
   *   consoleTaming?: 'safe' | 'unsafe',
   *   overrideTaming?: 'min' | 'moderate',
   *   stackFiltering?: 'concise' | 'verbose',
   * }} LockdownOptions
   */

  const { details: d$3, quote: q$2 } = assert;

  let firstOptions;

  // A successful lockdown call indicates that `harden` can be called and
  // guarantee that the hardened object graph is frozen out to the fringe.
  let lockedDown = false;

  // Build a harden() with an empty fringe.
  // Gate it on lockdown.
  const lockdownHarden = makeHardener();

  /**
   * @template T
   * @param {T} ref
   * @returns {T}
   */
  const harden = ref => {
    assert(lockedDown, 'Cannot harden before lockdown');
    return lockdownHarden(ref);
  };

  const alreadyHardenedIntrinsics = () => false;

  /**
   * @callback Transform
   * @param {string} source
   * @returns {string}
   */

  /**
   * @callback CompartmentConstructor
   * @param {Object} endowments
   * @param {Object} moduleMap
   * @param {Object} [options]
   * @param {Array<Transform>} [options.transforms]
   * @param {Array<Transform>} [options.__shimTransforms__]
   * @param {Object} [options.globalLexicals]
   */

  /**
   * @callback CompartmentConstructorMaker
   * @param {CompartmentConstructorMaker} targetMakeCompartmentConstructor
   * @param {Object} intrinsics
   * @param {(func: Function) => void} nativeBrander
   * @returns {CompartmentConstructor}
   */

  /**
   * @param {CompartmentConstructorMaker} makeCompartmentConstructor
   * @param {Object} compartmentPrototype
   * @param {() => Object} getAnonymousIntrinsics
   * @param {LockdownOptions} [options]
   * @returns {() => {}} repairIntrinsics
   */
  function repairIntrinsics(
    makeCompartmentConstructor,
    compartmentPrototype,
    getAnonymousIntrinsics,
    options = {},
  ) {
    // First time, absent options default to 'safe'.
    // Subsequent times, absent options default to first options.
    // Thus, all present options must agree with first options.
    // Reconstructing `option` here also ensures that it is a well
    // behaved record, with only own data properties.
    //
    // The `overrideTaming` is not a safety issue. Rather it is a tradeoff
    // between code compatibility, which is better with the `'moderate'`
    // setting, and tool compatibility, which is better with the `'min'`
    // setting. See
    // https://github.com/Agoric/SES-shim/blob/master/packages/ses/README.md#enabling-override-by-assignment)
    // for an explanation of when to use which.
    //
    // The `stackFiltering` is not a safety issue. Rather it is a tradeoff
    // between relevance and completeness of the stack frames shown on the
    // console. Setting`stackFiltering` to `'verbose'` applies no filters, providing
    // the raw stack frames that can be quite versbose. Setting
    // `stackFrameFiltering` to`'concise'` limits the display to the stack frame
    // information most likely to be relevant, eliminating distracting frames
    // such as those from the infrastructure. However, the bug you're trying to
    // track down might be in the infrastrure, in which case the `'verbose'` setting
    // is useful. See
    // [`stackFiltering` options](https://github.com/Agoric/SES-shim/blob/master/packages/ses/lockdown-options.md#stackfiltering-options)
    // for an explanation.
    options = /** @type {LockdownOptions} */ ({ ...firstOptions, ...options });
    const {
      dateTaming = 'safe',
      errorTaming = 'safe',
      mathTaming = 'safe',
      regExpTaming = 'safe',
      localeTaming = 'safe',
      consoleTaming = 'safe',
      overrideTaming = 'moderate',
      stackFiltering = 'concise',

      ...extraOptions
    } = options;

    // Assert that only supported options were passed.
    // Use Reflect.ownKeys to reject symbol-named properties as well.
    const extraOptionsNames = Reflect.ownKeys(extraOptions);
    assert(
      extraOptionsNames.length === 0,
      d$3`lockdown(): non supported option ${q$2(extraOptionsNames)}`,
    );

    // Asserts for multiple invocation of lockdown().
    if (firstOptions) {
      for (const name of keys(firstOptions)) {
        assert(
          options[name] === firstOptions[name],
          d$3`lockdown(): cannot re-invoke with different option ${q$2(name)}`,
        );
      }
      return alreadyHardenedIntrinsics;
    }

    firstOptions = {
      dateTaming,
      errorTaming,
      mathTaming,
      regExpTaming,
      localeTaming,
      consoleTaming,
      overrideTaming,
      stackFiltering,
    };

    /**
     * 1. TAME powers & gather intrinsics first.
     */
    const intrinsicsCollector = makeIntrinsicsCollector();

    intrinsicsCollector.addIntrinsics(tameFunctionConstructors());

    intrinsicsCollector.addIntrinsics(tameDateConstructor(dateTaming));
    intrinsicsCollector.addIntrinsics(
      tameErrorConstructor(errorTaming, stackFiltering),
    );
    intrinsicsCollector.addIntrinsics(tameMathObject(mathTaming));
    intrinsicsCollector.addIntrinsics(tameRegExpConstructor(regExpTaming));

    intrinsicsCollector.addIntrinsics(getAnonymousIntrinsics());

    intrinsicsCollector.completePrototypes();

    const intrinsics = intrinsicsCollector.finalIntrinsics();

    // Wrap console unless suppressed.
    // At the moment, the console is considered a host power in the start
    // compartment, and not a primordial. Hence it is absent from the whilelist
    // and bypasses the intrinsicsCollector.
    let optGetStackString;
    if (errorTaming !== 'unsafe') {
      optGetStackString = intrinsics['%InitialGetStackString%'];
    }
    const consoleRecord = tameConsole(consoleTaming, optGetStackString);
    globalThis.console = /** @type {Console} */ (consoleRecord.console);

    // Replace *Locale* methods with their non-locale equivalents
    tameLocaleMethods(intrinsics, localeTaming);

    // Replace Function.prototype.toString with one that recognizes
    // shimmed functions as honorary native functions.
    const nativeBrander = tameFunctionToString();

    /**
     * 2. WHITELIST to standardize the environment.
     */

    // Remove non-standard properties.
    // All remaining function encountered during whitelisting are
    // branded as honorary native functions.
    whitelistIntrinsics(intrinsics, nativeBrander);

    // Repair problems with legacy accessors if necessary.
    repairLegacyAccessors();

    // Initialize the powerful initial global, i.e., the global of the
    // start compartment, from the intrinsics.
    initGlobalObject(
      globalThis,
      intrinsics,
      initialGlobalPropertyNames,
      makeCompartmentConstructor,
      compartmentPrototype,
      {
        nativeBrander,
      },
    );

    /**
     * 3. HARDEN to share the intrinsics.
     */

    function hardenIntrinsics() {
      // Circumvent the override mistake.
      enablePropertyOverrides(intrinsics, overrideTaming);

      // Finally register and optionally freeze all the intrinsics. This
      // must be the operation that modifies the intrinsics.
      lockdownHarden(intrinsics);

      // Having completed lockdown without failing, the user may now
      // call `harden` and expect the object's transitively accessible properties
      // to be frozen out to the fringe.
      // Raise the `harden` gate.
      lockedDown = true;

      // Returning `true` indicates that this is a JS to SES transition.
      return true;
    }

    return hardenIntrinsics;
  }

  /**
   * @param {CompartmentConstructorMaker} makeCompartmentConstructor
   * @param {Object} compartmentPrototype
   * @param {() => Object} getAnonymousIntrinsics
   */
  const makeLockdown = (
    makeCompartmentConstructor,
    compartmentPrototype,
    getAnonymousIntrinsics,
  ) => {
    /**
     * @param {LockdownOptions} [options]
     */
    const lockdown = (options = {}) => {
      const maybeHardenIntrinsics = repairIntrinsics(
        makeCompartmentConstructor,
        compartmentPrototype,
        getAnonymousIntrinsics,
        options,
      );
      return maybeHardenIntrinsics();
    };
    return lockdown;
  };

  /** @typedef {ReturnType<typeof makeLockdown>} Lockdown */

  // @ts-check

  // privateFields captures the private state for each compartment.
  const privateFields = new WeakMap();

  /**
   * @typedef {(source: string) => string} Transform
   */

  const CompartmentPrototype = {
    constructor: InertCompartment,

    get globalThis() {
      return privateFields.get(this).globalObject;
    },

    get name() {
      return privateFields.get(this).name;
    },

    /**
     * @param {string} source is a JavaScript program grammar construction.
     * @param {Object} [options]
     * @param {Array<Transform>} [options.transforms]
     * @param {boolean} [options.sloppyGlobalsMode]
     * @param {Object} [options.__moduleShimLexicals__]
     * @param {boolean} [options.__evadeHtmlCommentTest__]
     * @param {boolean} [options.__evadeImportExpressionTest__]
     * @param {boolean} [options.__rejectSomeDirectEvalExpressions__]
     */
    evaluate(source, options = {}) {
      // Perform this check first to avoid unecessary sanitizing.
      // TODO Maybe relax string check and coerce instead:
      // https://github.com/tc39/proposal-dynamic-code-brand-checks
      if (typeof source !== 'string') {
        throw new TypeError('first argument of evaluate() must be a string');
      }

      // Extract options, and shallow-clone transforms.
      const {
        transforms = [],
        sloppyGlobalsMode = false,
        __moduleShimLexicals__ = undefined,
        __evadeHtmlCommentTest__ = false,
        __evadeImportExpressionTest__ = false,
        __rejectSomeDirectEvalExpressions__ = true, // Note default on
      } = options;
      const localTransforms = [...transforms];
      if (__evadeHtmlCommentTest__ === true) {
        localTransforms.push(evadeHtmlCommentTest);
      }
      if (__evadeImportExpressionTest__ === true) {
        localTransforms.push(evadeImportExpressionTest);
      }
      if (__rejectSomeDirectEvalExpressions__ === true) {
        localTransforms.push(rejectSomeDirectEvalExpressions);
      }

      const compartmentFields = privateFields.get(this);
      let { globalTransforms } = compartmentFields;
      const {
        globalObject,
        globalLexicals,
        knownScopeProxies,
      } = compartmentFields;

      let localObject = globalLexicals;
      if (__moduleShimLexicals__ !== undefined) {
        // When using `evaluate` for ESM modules, as should only occur from the
        // module-shim's module-instance.js, we do not reveal the SES-shim's
        // module-to-program translation, as this is not standardizable behavior.
        // However, the `localTransforms` will come from the `__shimTransforms__`
        // Compartment option in this case, which is a non-standardizable escape
        // hatch so programs designed specifically for the SES-shim
        // implementation may opt-in to use the same transforms for `evaluate`
        // and `import`, at the expense of being tightly coupled to SES-shim.
        globalTransforms = undefined;

        localObject = create(null, getOwnPropertyDescriptors(globalLexicals));
        defineProperties(
          localObject,
          getOwnPropertyDescriptors(__moduleShimLexicals__),
        );
      }

      return performEval(source, globalObject, localObject, {
        globalTransforms,
        localTransforms,
        sloppyGlobalsMode,
        knownScopeProxies,
      });
    },

    toString() {
      return '[object Compartment]';
    },

    /* eslint-disable-next-line no-underscore-dangle */
    __isKnownScopeProxy__(value) {
      return privateFields.get(this).knownScopeProxies.has(value);
    },
  };

  defineProperties(InertCompartment, {
    prototype: { value: CompartmentPrototype },
  });

  /**
   * @callback CompartmentConstructor
   * Each Compartment constructor is a global. A host that wants to execute
   * code in a context bound to a new global creates a new compartment.
   *
   * @param {Object} endowments
   * @param {Object} _moduleMap
   * @param {Object} [options]
   * @param {string} [options.name]
   * @param {Array<Transform>} [options.transforms]
   * @param {Array<Transform>} [options.__shimTransforms__]
   * @param {Object} [options.globalLexicals]
   */

  /**
   * @callback MakeCompartmentConstructor
   * @param {MakeCompartmentConstructor} targetMakeCompartmentConstructor
   * @param {Object} intrinsics
   * @param {(object: Object) => void} nativeBrander
   * @returns {CompartmentConstructor}
   */

  /** @type {MakeCompartmentConstructor} */
  const makeCompartmentConstructor = (
    targetMakeCompartmentConstructor,
    intrinsics,
    nativeBrander,
  ) => {
    /** @type {CompartmentConstructor} */
    function Compartment(endowments = {}, _moduleMap = {}, options = {}) {
      if (new.target === undefined) {
        throw new TypeError(
          "Class constructor Compartment cannot be invoked without 'new'",
        );
      }

      // Extract options, and shallow-clone transforms.
      const {
        name = '<unknown>',
        transforms = [],
        __shimTransforms__ = [],
        globalLexicals = {},
      } = options;
      const globalTransforms = [...transforms, ...__shimTransforms__];

      const globalObject = {};
      initGlobalObject(
        globalObject,
        intrinsics,
        sharedGlobalPropertyNames,
        targetMakeCompartmentConstructor,
        this.constructor.prototype,
        {
          globalTransforms,
          nativeBrander,
        },
      );

      assign(globalObject, endowments);

      const invalidNames = getOwnPropertyNames(globalLexicals).filter(
        identifier => !isValidIdentifierName(identifier),
      );
      if (invalidNames.length) {
        throw new Error(
          `Cannot create compartment with invalid names for global lexicals: ${invalidNames.join(
          ', ',
        )}; these names would not be lexically mentionable`,
        );
      }

      const knownScopeProxies = new WeakSet();
      privateFields.set(this, {
        name,
        globalTransforms,
        globalObject,
        knownScopeProxies,
        // The caller continues to own the globalLexicals object they passed to
        // the compartment constructor, but the compartment only respects the
        // original values and they are constants in the scope of evaluated
        // programs and executed modules.
        // This shallow copy captures only the values of enumerable own
        // properties, erasing accessors.
        // The snapshot is frozen to ensure that the properties are immutable
        // when transferred-by-property-descriptor onto local scope objects.
        globalLexicals: freeze({ ...globalLexicals }),
      });
    }

    Compartment.prototype = CompartmentPrototype;

    return Compartment;
  };

  // Copyright (C) 2018 Agoric

  const nativeBrander$1 = tameFunctionToString();

  const Compartment = makeCompartmentConstructor(
    makeCompartmentConstructor,
    getGlobalIntrinsics(globalThis),
    nativeBrander$1,
  );

  assign(globalThis, {
    harden,
    lockdown: makeLockdown(
      makeCompartmentConstructor,
      CompartmentPrototype,
      getAnonymousIntrinsics,
    ),
    Compartment,
    assert,
  });

})));

// END of injected code from ses
  })()
  return module.exports
})()

    const lockdownOptions = {
      // gives a semi-high resolution timer
      dateTaming: 'unsafe',
      // this is introduces non-determinism, but is otherwise safe
      mathTaming: 'unsafe',
      // lets code observe call stack, but easier debuggability
      errorTaming: 'unsafe',
      // shows the full call stack
      stackFiltering: 'verbose',
    }

    lockdown(lockdownOptions)

    // initialize the kernel
    const createKernelCore = (function () {
  return createKernel

  function createKernel ({
    // the platform api global
    globalRef,
    // package policy object
    lavamoatConfig,
    // kernel configuration
    loadModuleData,
    getRelativeModuleId,
    prepareModuleInitializerArgs,
    getExternalCompartment,
    globalThisRefs,
    // security options
    debugMode
  }) {
    // create SES-wrapped LavaMoat kernel
    // endowments:
    // - console is included for convenience
    // - Math is for untamed Math.random
    // - Date is for untamed Date.now
    const kernelCompartment = new Compartment({ console, Math, Date })
    const makeKernel = kernelCompartment.evaluate(`(${unsafeCreateKernel})\n//# sourceURL=LavaMoat/core/kernel`)
    const lavamoatKernel = makeKernel({
      globalRef,
      lavamoatConfig,
      loadModuleData,
      getRelativeModuleId,
      prepareModuleInitializerArgs,
      getExternalCompartment,
      globalThisRefs,
      debugMode
    })

    return lavamoatKernel
  }

  // this is serialized and run in SES
  // mostly just exists to expose variables to internalRequire and loadBundle
  function unsafeCreateKernel ({
    globalRef,
    debugMode,
    lavamoatConfig,
    loadModuleData,
    getRelativeModuleId,
    prepareModuleInitializerArgs,
    getExternalCompartment,
    globalThisRefs = ['globalThis']
  }) {
    // "templateRequire" calls are inlined in "generatePrelude"
    const generalUtils = // define makeGeneralUtils
(function(){
  const global = globalRef
  const exports = {}
  const module = { exports }
  ;(function(){
// START of injected code from makeGeneralUtils
module.exports = makeGeneralUtils

function makeGeneralUtils () {
  return {
    createFunctionWrapper
  }

  function createFunctionWrapper (sourceValue, unwrapTest, unwrapTo) {
    const newValue = function (...args) {
      if (new.target) {
        // handle constructor calls
        return Reflect.construct(sourceValue, args, new.target)
      } else {
        // handle function calls
        // unwrap to target value if this value is the source package compartment's globalThis
        const thisRef = unwrapTest(this) ? unwrapTo : this
        return Reflect.apply(sourceValue, thisRef, args)
      }
    }
    Object.defineProperties(newValue, Object.getOwnPropertyDescriptors(sourceValue))
    return newValue
  }
}
// END of injected code from makeGeneralUtils
  })()
  return module.exports
})()()
    const { getEndowmentsForConfig, makeMinimalViewOfRef, applyEndowmentPropDescTransforms } = // define makeGetEndowmentsForConfig
(function(){
  const global = globalRef
  const exports = {}
  const module = { exports }
  ;(function(){
// START of injected code from makeGetEndowmentsForConfig
// the contents of this file will be copied into the prelude template
// this module has been written so that it required directly or copied and added to the template with a small wrapper
module.exports = makeGetEndowmentsForConfig

// utilities for generating the endowments object based on a globalRef and a config

// The config uses a period-deliminated path notation to pull out deep values from objects
// These utilities help create an object populated with only the deep properties specified in the config

function makeGetEndowmentsForConfig ({ createFunctionWrapper }) {
  return {
    getEndowmentsForConfig,
    makeMinimalViewOfRef,
    copyValueAtPath,
    applyGetSetPropDescTransforms,
    applyEndowmentPropDescTransforms
  }

  /**
   *
   * @function getEndowmentsForConfig
   * @param {object} sourceRef - Object from which to copy properties
   * @param {object} config - LavaMoat package config
   * @param {object} unwrapTo - For getters and setters, when the this-value is unwrapFrom, is replaced as unwrapTo
   * @param {object} unwrapFrom - For getters and setters, the this-value to replace (default: targetRef)
   * @return {object} - The targetRef
   *
   */
  function getEndowmentsForConfig (sourceRef, config, unwrapTo, unwrapFrom) {
    if (!config.globals) return {}
    // validate read access from config
    const whitelistedReads = []
    Object.entries(config.globals).forEach(([path, configValue]) => {
      const pathParts = path.split('.')
      // disallow dunder proto in path
      const pathContainsDunderProto = pathParts.some(pathPart => pathPart === '__proto__')
      if (pathContainsDunderProto) {
        throw new Error(`Lavamoat - "__proto__" disallowed when creating minial view. saw "${path}"`)
      }
      // write access handled elsewhere
      if (configValue === 'write') return
      if (configValue !== true) {
        throw new Error(`LavaMoat - unknown value for config (${typeof configValue})`)
      }
      whitelistedReads.push(path)
    })
    return makeMinimalViewOfRef(sourceRef, whitelistedReads, unwrapTo, unwrapFrom)
  }

  function makeMinimalViewOfRef (sourceRef, paths, unwrapTo, unwrapFrom) {
    const targetRef = {}
    paths.forEach(path => {
      copyValueAtPath(path.split('.'), sourceRef, targetRef, unwrapTo, unwrapFrom)
    })
    return targetRef
  }

  function copyValueAtPath (pathParts, sourceRef, targetRef, unwrapTo = sourceRef, unwrapFrom = targetRef) {
    if (pathParts.length === 0) {
      throw new Error('unable to copy, must have pathParts, was empty')
    }
    const [nextPart, ...remainingParts] = pathParts
    // get the property from any depth in the property chain
    const { prop: sourcePropDesc } = getPropertyDescriptorDeep(sourceRef, nextPart)

    // if source missing the value to copy, just skip it
    if (!sourcePropDesc) {
      return
    }

    // if target already has a value, it must be extensible
    const targetPropDesc = Reflect.getOwnPropertyDescriptor(targetRef, nextPart)
    if (targetPropDesc) {
      // dont attempt to extend a getter or trigger a setter
      if (!('value' in targetPropDesc)) {
        throw new Error(`unable to copy on to targetRef, targetRef has a getter at "${nextPart}"`)
      }
      // value must be extensible (cant write properties onto it)
      const targetValue = targetPropDesc.value
      const valueType = typeof targetValue
      if (valueType !== 'object' && valueType !== 'function') {
        throw new Error(`unable to copy on to targetRef, targetRef value is not an obj or func "${nextPart}"`)
      }
    }

    // if this is not the last path in the assignment, walk into the containing reference
    if (remainingParts.length > 0) {
      const { sourceValue, sourceWritable } = getSourceValue()
      const nextSourceRef = sourceValue
      let nextTargetRef
      // check if value exists on target
      if (targetPropDesc) {
        // a value already exists, we should walk into it
        nextTargetRef = targetPropDesc.value
      } else {
        // its not populated so lets write to it
        // put an object to serve as a container
        const containerRef = {}
        const newPropDesc = {
          value: containerRef,
          writable: sourceWritable,
          enumerable: sourcePropDesc.enumerable,
          configurable: sourcePropDesc.configurable
        }
        Reflect.defineProperty(targetRef, nextPart, newPropDesc)
        // the newly created container will be the next target
        nextTargetRef = containerRef
      }
      copyValueAtPath(remainingParts, nextSourceRef, nextTargetRef)
      return
    }

    // this is the last part of the path, the value we're trying to actually copy
    // if has getter/setter - apply this-value unwrapping
    if (!('value' in sourcePropDesc)) {
      // wrapper setter/getter with correct receiver
      const wrapperPropDesc = applyGetSetPropDescTransforms(sourcePropDesc, unwrapFrom, unwrapTo)
      Reflect.defineProperty(targetRef, nextPart, wrapperPropDesc)
      return
    }

    // need to determine the value type in order to copy it with
    // this-value unwrapping support
    const { sourceValue, sourceWritable } = getSourceValue()

    // not a function - copy as is
    if (typeof sourceValue !== 'function') {
      Reflect.defineProperty(targetRef, nextPart, sourcePropDesc)
      return
    }
    // otherwise add workaround for functions to swap back to the sourceal "this" reference
    const unwrapTest = thisValue => thisValue === unwrapFrom
    const newValue = createFunctionWrapper(sourceValue, unwrapTest, unwrapTo)
    const newPropDesc = {
      value: newValue,
      writable: sourceWritable,
      enumerable: sourcePropDesc.enumerable,
      configurable: sourcePropDesc.configurable
    }
    Reflect.defineProperty(targetRef, nextPart, newPropDesc)

    function getSourceValue () {
      // determine the source value, this coerces getters to values
      // im deeply sorry, respecting getters was complicated and
      // my brain is not very good
      let sourceValue, sourceWritable
      if ('value' in sourcePropDesc) {
        sourceValue = sourcePropDesc.value
        sourceWritable = sourcePropDesc.writable
      } else if ('get' in sourcePropDesc) {
        sourceValue = sourcePropDesc.get.call(unwrapTo)
        sourceWritable = 'set' in sourcePropDesc
      } else {
        throw new Error('getEndowmentsForConfig - property descriptor missing a getter')
      }
      return { sourceValue, sourceWritable }
    }
  }

  function applyEndowmentPropDescTransforms (propDesc, unwrapFromCompartment, unwrapToGlobalThis) {
    let newPropDesc = propDesc
    newPropDesc = applyFunctionPropDescTransform(newPropDesc, unwrapFromCompartment, unwrapToGlobalThis)
    newPropDesc = applyGetSetPropDescTransforms(newPropDesc, unwrapFromCompartment.globalThis, unwrapToGlobalThis)
    return newPropDesc
  }

  function applyGetSetPropDescTransforms (sourcePropDesc, unwrapFromGlobalThis, unwrapToGlobalThis) {
    const wrappedPropDesc = { ...sourcePropDesc }
    if (sourcePropDesc.get) {
      wrappedPropDesc.get = function () {
        const receiver = this
        // replace the "receiver" value if it points to fake parent
        const receiverRef = receiver === unwrapFromGlobalThis ? unwrapToGlobalThis : receiver
        // sometimes getters replace themselves with static properties, as seen wih the FireFox runtime
        const result = Reflect.apply(sourcePropDesc.get, receiverRef, [])
        if (typeof result === 'function') {
          // functions must be wrapped to ensure a good this-value.
          // lockdown causes some propDescs to go to value -> getter,
          // eg "Function.prototype.bind". we need to wrap getter results
          // as well in order to ensure they have their this-value wrapped correctly
          // if this ends up being problematic we can maybe take advantage of lockdown's
          // "getter.originalValue" property being available
          return createFunctionWrapper(result, (thisValue) => thisValue === unwrapFromGlobalThis, unwrapToGlobalThis)
        } else {
          return result
        }
      }
    }
    if (sourcePropDesc.set) {
      wrappedPropDesc.set = function (value) {
        // replace the "receiver" value if it points to fake parent
        const receiver = this
        const receiverRef = receiver === unwrapFromGlobalThis ? unwrapToGlobalThis : receiver
        return Reflect.apply(sourcePropDesc.set, receiverRef, [value])
      }
    }
    return wrappedPropDesc
  }

  function applyFunctionPropDescTransform (propDesc, unwrapFromCompartment, unwrapToGlobalThis) {
    if (!('value' in propDesc && typeof propDesc.value === 'function')) {
      return propDesc
    }
    const unwrapTest = (thisValue) => {
      // unwrap function calls this-value to unwrapToGlobalThis when:
      // this value is globalThis ex. globalThis.abc()
      // scope proxy leak workaround ex. abc()
      return thisValue === unwrapFromCompartment.globalThis || unwrapFromCompartment.__isKnownScopeProxy__(thisValue)
    }
    const newFn = createFunctionWrapper(propDesc.value, unwrapTest, unwrapToGlobalThis)
    return { ...propDesc, value: newFn }
  }
}

function getPropertyDescriptorDeep (target, key) {
  let receiver = target
  while (true) {
    // support lookup on objects and primitives
    const typeofReceiver = typeof receiver
    if (typeofReceiver === 'object' || typeofReceiver === 'function') {
      const prop = Reflect.getOwnPropertyDescriptor(receiver, key)
      if (prop) {
        return { receiver, prop }
      }
      // try next in the prototype chain
      receiver = Reflect.getPrototypeOf(receiver)
    } else {
      // prototype lookup for primitives
      // eslint-disable-next-line no-proto
      receiver = receiver.__proto__
    }
    // abort if this is the end of the prototype chain.
    if (!receiver) return { prop: null, receiver: null }
  }
}

// END of injected code from makeGetEndowmentsForConfig
  })()
  return module.exports
})()(generalUtils)
    const { prepareCompartmentGlobalFromConfig } = // define makePrepareRealmGlobalFromConfig
(function(){
  const global = globalRef
  const exports = {}
  const module = { exports }
  ;(function(){
// START of injected code from makePrepareRealmGlobalFromConfig
// the contents of this file will be copied into the prelude template
// this module has been written so that it required directly or copied and added to the template with a small wrapper
module.exports = makePrepareRealmGlobalFromConfig

// utilities for exposing configuring the exposed endowments on the container global

// The config uses a period-deliminated path notation to pull out deep values from objects
// These utilities help modify the container global to expose the allowed globals from the globalStore OR the platform global

function makePrepareRealmGlobalFromConfig ({ createFunctionWrapper }) {
  return {
    prepareCompartmentGlobalFromConfig,
    getTopLevelReadAccessFromPackageConfig,
    getTopLevelWriteAccessFromPackageConfig
  }

  function getTopLevelReadAccessFromPackageConfig (globalsConfig) {
    const result = Object.entries(globalsConfig)
      .filter(([key, value]) => value === 'read' || value === true || (value === 'write' && key.split('.').length > 1))
      .map(([key]) => key.split('.')[0])
    // return unique array
    return Array.from(new Set(result))
  }

  function getTopLevelWriteAccessFromPackageConfig (globalsConfig) {
    const result = Object.entries(globalsConfig)
      .filter(([key, value]) => value === 'write' && key.split('.').length === 1)
      .map(([key]) => key)
    return result
  }

  function prepareCompartmentGlobalFromConfig (packageCompartment, globalsConfig, endowments, globalStore, globalThisRefs) {
    const packageCompartmentGlobal = packageCompartment.globalThis
    // lookup top level read + write access keys
    const topLevelWriteAccessKeys = getTopLevelWriteAccessFromPackageConfig(globalsConfig)
    const topLevelReadAccessKeys = getTopLevelReadAccessFromPackageConfig(globalsConfig)

    // define accessors

    // allow read access via globalStore or packageCompartmentGlobal
    topLevelReadAccessKeys.forEach(key => {
      Object.defineProperty(packageCompartmentGlobal, key, {
        get () {
          if (globalStore.has(key)) {
            return globalStore.get(key)
          } else {
            return Reflect.get(endowments, key, this)
          }
        },
        set () {
          // TODO: there should be a config to throw vs silently ignore
          console.warn(`LavaMoat: ignoring write attempt to read-access global "${key}"`)
        }
      })
    })

    // allow write access to globalStore
    // read access via globalStore or packageCompartmentGlobal
    topLevelWriteAccessKeys.forEach(key => {
      Object.defineProperty(packageCompartmentGlobal, key, {
        get () {
          if (globalStore.has(key)) {
            return globalStore.get(key)
          } else {
            return endowments[key]
          }
        },
        set (value) {
          globalStore.set(key, value)
        },
        enumerable: true,
        configurable: true
      })
    })

    // set circular globalRefs
    globalThisRefs.forEach(key => {
      // if globalRef is actually an endowment, ignore
      if (topLevelReadAccessKeys.includes(key)) return
      if (topLevelWriteAccessKeys.includes(key)) return
      // set circular ref to global
      packageCompartmentGlobal[key] = packageCompartmentGlobal
    })

    // bind Function constructor this value to globalThis
    // legacy globalThis shim
    const origFunction = packageCompartmentGlobal.Function
    const newFunction = function (...args) {
      const fn = origFunction(...args)
      const unwrapTest = thisValue => thisValue === undefined
      return createFunctionWrapper(fn, unwrapTest, packageCompartmentGlobal)
    }
    Object.defineProperties(newFunction, Object.getOwnPropertyDescriptors(origFunction))
    packageCompartmentGlobal.Function = newFunction
  }
}

// END of injected code from makePrepareRealmGlobalFromConfig
  })()
  return module.exports
})()(generalUtils)

    const moduleCache = new Map()
    const packageCompartmentCache = new Map()
    const globalStore = new Map()

    const rootPackageName = '<root>'
    const rootPackageCompartment = createRootPackageCompartment(globalRef)

    return {
      internalRequire
    }

    // this function instantiaties a module from a moduleId.
    // 1. loads the module metadata and policy
    // 2. prepares the execution environment
    // 3. instantiates the module, recursively instantiating dependencies
    // 4. returns the module exports
    function internalRequire (moduleId) {
      // use cached module.exports if module is already instantiated
      if (moduleCache.has(moduleId)) {
        const moduleExports = moduleCache.get(moduleId).exports
        return moduleExports
      }

      // load and validate module metadata
      // if module metadata is missing, throw an error
      const moduleData = loadModuleData(moduleId)
      if (!moduleData) {
        const err = new Error('Cannot find module \'' + moduleId + '\'')
        err.code = 'MODULE_NOT_FOUND'
        throw err
      }
      if (moduleData.id === undefined) {
        throw new Error('LavaMoat - moduleId is not defined correctly.')
      }

      // parse and validate module data
      const { package: packageName, source: moduleSource } = moduleData
      if (!packageName) throw new Error(`LavaMoat - invalid packageName for module "${moduleId}"`)
      const packagePolicy = getPolicyForPackage(lavamoatConfig, packageName)

      // create the moduleObj and initializer
      const { moduleInitializer, moduleObj } = prepareModuleInitializer(moduleData, packagePolicy)

      // cache moduleObj here
      // this is important to inf loops when hitting cycles in the dep graph
      // must cache before running the moduleInitializer
      moduleCache.set(moduleId, moduleObj)

      // validate moduleInitializer
      if (typeof moduleInitializer !== 'function') {
        throw new Error(`LavaMoat - moduleInitializer is not defined correctly. got "${typeof moduleInitializer}"\n${moduleSource}`)
      }

      // initialize the module with the correct context
      const initializerArgs = prepareModuleInitializerArgs(requireRelativeWithContext, moduleObj, moduleData)
      moduleInitializer.apply(moduleObj.exports, initializerArgs)
      const moduleExports = moduleObj.exports

      return moduleExports

      // this is passed to the module initializer
      // it adds the context of the parent module
      // this could be replaced via "Function.prototype.bind" if its more performant
      function requireRelativeWithContext (requestedName) {
        const parentModuleExports = moduleObj.exports
        const parentModuleData = moduleData
        const parentPackagePolicy = packagePolicy
        const parentModuleId = moduleId
        return requireRelative({ requestedName, parentModuleExports, parentModuleData, parentPackagePolicy, parentModuleId })
      }
    }

    // this resolves a module given a requestedName (eg relative path to parent) and a parentModule context
    // the exports are processed via "protectExportsRequireTime" per the module's configuration
    function requireRelative ({ requestedName, parentModuleExports, parentModuleData, parentPackagePolicy, parentModuleId }) {
      const parentModulePackageName = parentModuleData.package
      const parentPackagesWhitelist = parentPackagePolicy.packages
      const parentBuiltinsWhitelist = Object.entries(parentPackagePolicy.builtin)
        .filter(([_, allowed]) => allowed === true)
        .map(([packagePath, allowed]) => packagePath.split('.')[0])

      // resolve the moduleId from the requestedName
      const moduleId = getRelativeModuleId(parentModuleId, requestedName)

      // browserify goop:
      // recursive requires dont hit cache so it inf loops, so we shortcircuit
      // this only seems to happen with a few browserify builtins (nodejs builtin module polyfills)
      // we could likely allow any requestedName since it can only refer to itself
      if (moduleId === parentModuleId) {
        if (['timers', 'buffer'].includes(requestedName) === false) {
          throw new Error(`LavaMoat - recursive require detected: "${requestedName}"`)
        }
        return parentModuleExports
      }

      // load module
      let moduleExports = internalRequire(moduleId)

      // look up config for module
      const moduleData = loadModuleData(moduleId)
      const packageName = moduleData.package

      // disallow requiring packages that are not in the parent's whitelist
      const isSamePackage = packageName === parentModulePackageName
      const parentIsEntryModule = parentModulePackageName === rootPackageName
      let isInParentWhitelist = false
      if (moduleData.type === 'builtin') {
        isInParentWhitelist = parentBuiltinsWhitelist.includes(packageName)
      } else {
        isInParentWhitelist = (parentPackagesWhitelist[packageName] === true)
      }

      // validate that the import is allowed
      if (!parentIsEntryModule && !isSamePackage && !isInParentWhitelist) {
        let typeText = ' '
        if (moduleData.type === 'builtin') typeText = ' node builtin '
        throw new Error(`LavaMoat - required${typeText}package not in whitelist: package "${parentModulePackageName}" requested "${packageName}" as "${requestedName}"`)
      }

      // create minimal selection if its a builtin and the whole path is not selected for
      if (!parentIsEntryModule && moduleData.type === 'builtin' && !parentPackagePolicy.builtin[moduleId]) {
        const builtinPaths = (
          Object.entries(parentPackagePolicy.builtin)
          // grab all allowed builtin paths that match this package
            .filter(([packagePath, allowed]) => allowed === true && moduleId === packagePath.split('.')[0])
          // only include the paths after the packageName
            .map(([packagePath, allowed]) => packagePath.split('.').slice(1).join('.'))
            .sort()
        )
        moduleExports = makeMinimalViewOfRef(moduleExports, builtinPaths)
      }

      return moduleExports
    }

    function prepareModuleInitializer (moduleData, packagePolicy) {
      const { moduleInitializer, package: packageName, id: moduleId, source: moduleSource } = moduleData

      // moduleInitializer may be set by loadModuleData (e.g. builtin + native modules)
      if (moduleInitializer) {
        // if an external moduleInitializer is set, ensure it is allowed
        if (moduleData.type === 'native') {
          // ensure package is allowed to have native modules
          if (packagePolicy.native !== true) {
            throw new Error(`LavaMoat - "native" module type not permitted for package "${packageName}", module "${moduleId}"`)
          }
        } else if (moduleData.type !== 'builtin') {
          // builtin module types dont have policy configurations
          // but the packages that can import them are constrained elsewhere
          // here we just ensure that the module type is the only other type with a external moduleInitializer
          throw new Error(`LavaMoat - invalid external moduleInitializer for module type "${moduleData.type}" in package "${packageName}", module "${moduleId}"`)
        }
        // moduleObj must be from the same Realm as the moduleInitializer
        // here we are assuming the provided moduleInitializer is from the same Realm as this kernel
        const moduleObj = { exports: {} }
        return { moduleInitializer, moduleObj }
      }

      // setup initializer from moduleSource and compartment.
      // execute in package compartment with globalThis populated per package policy
      const packageCompartment = getCompartmentForPackage(packageName, packagePolicy)
      // TODO: move all source mutations elsewhere
      try {
        const sourceURL = moduleData.file || `modules/${moduleId}`
        if (sourceURL.includes('\n')) {
          throw new Error(`LavaMoat - Newlines not allowed in filenames: ${JSON.stringify(sourceURL)}`)
        }
        // moduleObj must be from the same Realm as the moduleInitializer
        // the dart2js runtime relies on this for some reason
        const moduleObj = packageCompartment.evaluate('({ exports: {} })')
        const moduleInitializer = packageCompartment.evaluate(`${moduleSource}\n//# sourceURL=${sourceURL}`)
        return { moduleInitializer, moduleObj }
      } catch (err) {
        console.warn(`LavaMoat - Error evaluating module "${moduleId}" from package "${packageName}" \n${err.stack}`)
        throw err
      }
    }

    function createRootPackageCompartment (globalRef) {
      if (packageCompartmentCache.has(rootPackageName)) {
        throw new Error('LavaMoat - createRootPackageCompartment called more than once')
      }
      // prepare the root package's SES Compartment
      // endowments:
      // - Math is for untamed Math.random
      // - Date is for untamed Date.now
      const rootPackageCompartment = new Compartment({ Math, Date })
      // find the relevant endowment sources
      const globalProtoChain = getPrototypeChain(globalRef)
      // the index for the common prototypal ancestor, Object.prototype
      // this should always be the last index, but we check just in case
      const commonPrototypeIndex = globalProtoChain.findIndex(globalProtoChainEntry => globalProtoChainEntry === Object.prototype)
      if (commonPrototypeIndex === -1) throw new Error('Lavamoat - unable to find common prototype between Compartment and globalRef')
      // we will copy endowments from all entries in the prototype chain, excluding Object.prototype
      const endowmentSources = globalProtoChain.slice(0, commonPrototypeIndex)

      // call all getters, in case of behavior change (such as with FireFox lazy getters)
      // call on contents of endowmentsSources directly instead of in new array instances. If there is a lazy getter it only changes the original prop desc.
      endowmentSources.forEach(source => {
        const descriptors = Object.getOwnPropertyDescriptors(source)
        Object.values(descriptors).forEach(desc => {
          if ('get' in desc) {
            Reflect.apply(desc.get, globalRef, [])
          }
        })
      })

      const endowmentSourceDescriptors = endowmentSources.map(globalProtoChainEntry => Object.getOwnPropertyDescriptors(globalProtoChainEntry))
      // flatten propDesc collections with precedence for globalThis-end of the prototype chain
      const endowmentDescriptorsFlat = Object.assign(Object.create(null), ...endowmentSourceDescriptors.reverse())
      // expose all own properties of globalRef, including non-enumerable
      Object.entries(endowmentDescriptorsFlat)
        // ignore properties already defined on compartment global
        .filter(([key]) => !(key in rootPackageCompartment.globalThis))
        // ignore circular globalThis refs
        .filter(([key]) => !(globalThisRefs.includes(key)))
        // define property on compartment global
        .forEach(([key, desc]) => {
          // unwrap functions, setters/getters & apply scope proxy workaround
          const wrappedPropDesc = applyEndowmentPropDescTransforms(desc, rootPackageCompartment, globalRef)
          Reflect.defineProperty(rootPackageCompartment.globalThis, key, wrappedPropDesc)
        })
      // global circular references otherwise added by prepareCompartmentGlobalFromConfig
      // Add all circular refs to root package compartment globalThis
      for (const ref of globalThisRefs) {
        if (ref in rootPackageCompartment.globalThis) {
          continue
        }
        rootPackageCompartment.globalThis[ref] = rootPackageCompartment.globalThis
      }

      // save the compartment for use by other modules in the package
      packageCompartmentCache.set(rootPackageName, rootPackageCompartment)

      return rootPackageCompartment
    }

    function getCompartmentForPackage (packageName, packagePolicy) {
      // compartment may have already been created
      let packageCompartment = packageCompartmentCache.get(packageName)
      if (packageCompartment) {
        return packageCompartment
      }

      // prepare Compartment
      if (getExternalCompartment && packagePolicy.env) {
        // external compartment can be provided by the platform (eg lavamoat-node)
        packageCompartment = getExternalCompartment(packageName, packagePolicy)
      } else {
        // prepare the module's SES Compartment
        // endowments:
        // - Math is for untamed Math.random
        // - Date is for untamed Date.now
        packageCompartment = new Compartment({ Math, Date })
      }
      // prepare endowments
      let endowments
      try {
        endowments = getEndowmentsForConfig(
          // source reference
          rootPackageCompartment.globalThis,
          // policy
          packagePolicy,
          // unwrap to
          globalRef,
          // unwrap from
          packageCompartment.globalThis
        )
      } catch (err) {
        const errMsg = `Lavamoat - failed to prepare endowments for package "${packageName}":\n${err.stack}`
        throw new Error(errMsg)
      }

      // transform functions, getters & setters on prop descs. Solves SES scope proxy bug
      Object.entries(Object.getOwnPropertyDescriptors(endowments))
        // ignore non-configurable properties because we are modifying endowments in place
        .filter(([key, propDesc]) => propDesc.configurable)
        .forEach(([key, propDesc]) => {
          const wrappedPropDesc = applyEndowmentPropDescTransforms(propDesc, packageCompartment, rootPackageCompartment.globalThis)
          Reflect.defineProperty(endowments, key, wrappedPropDesc)
        })

      // sets up read/write access as configured
      const globalsConfig = packagePolicy.globals
      prepareCompartmentGlobalFromConfig(packageCompartment, globalsConfig, endowments, globalStore, globalThisRefs)

      // save the compartment for use by other modules in the package
      packageCompartmentCache.set(packageName, packageCompartment)

      return packageCompartment
    }

    // this gets the lavaMoat config for a module by packageName
    // if there were global defaults (e.g. everything gets "console") they could be applied here
    function getPolicyForPackage (config, packageName) {
      const packageConfig = (config.resources || {})[packageName] || {}
      packageConfig.globals = packageConfig.globals || {}
      packageConfig.packages = packageConfig.packages || {}
      packageConfig.builtin = packageConfig.builtin || {}
      return packageConfig
    }

    // util for getting the prototype chain as an array
    // includes the provided value in the result
    function getPrototypeChain (value) {
      const protoChain = []
      let current = value
      while (current && (typeof current === 'object' || typeof current === 'function')) {
        protoChain.push(current)
        current = Reflect.getPrototypeOf(current)
      }
      return protoChain
    }
  }
})()

    const kernel = createKernelCore({
      lavamoatConfig,
      loadModuleData,
      getRelativeModuleId,
      prepareModuleInitializerArgs,
      getExternalCompartment,
      globalRef,
      globalThisRefs,
      debugMode
    })
    return kernel
  }
})()

  const { internalRequire } = createKernel({
    lavamoatConfig,
    loadModuleData,
    getRelativeModuleId,
    prepareModuleInitializerArgs,
    globalThisRefs: ['window', 'self', 'global', 'globalThis']
  })

  // create a lavamoat pulic API for loading modules over multiple files
  const lavamoatPublicApi = Object.freeze({
    loadBundle: Object.freeze(loadBundle),
  })
  globalRef.LavaMoat = lavamoatPublicApi

  return loadBundle


  // it is called by the modules collection that will be appended to this file
  function loadBundle (newModules, entryPoints, newConfig) {
    // verify + load config
    Object.entries(newConfig.resources || {}).forEach(([packageName, packageConfig]) => {
      if (packageName in lavamoatConfig) {
        throw new Error(`LavaMoat - loadBundle encountered redundant config definition for package "${packageName}"`)
      }
      lavamoatConfig.resources[packageName] = packageConfig
    })
    // verify + load in each module
    for (const [moduleId, moduleData] of Object.entries(newModules)) {
      // verify that module is new
      if (moduleId in modules) {
        throw new Error(`LavaMoat - loadBundle encountered redundant module definition for id "${moduleId}"`)
      }
      // add the module
      modules[moduleId] = moduleData
    }
    // run each of entryPoints
    const entryExports = Array.prototype.map.call(entryPoints, (entryId) => {
      return internalRequire(entryId)
    })
    // webpack compat: return the first module's exports
    return entryExports[0]
  }

  function loadModuleData (moduleId) {
    return modules[moduleId]
  }

  function getRelativeModuleId (parentModuleId, requestedName) {
    const parentModuleData = modules[parentModuleId]
    if (!(requestedName in parentModuleData.deps)) {
      console.warn(`missing dep: ${parentModuleData.package} requested ${requestedName}`)
    }
    return parentModuleData.deps[requestedName] || requestedName
  }

  function prepareModuleInitializerArgs (requireRelativeWithContext, moduleObj, moduleData) {
    const require = requireRelativeWithContext
    const module = moduleObj
    const exports = moduleObj.exports

    // browserify goop:
    // this "modules" interface is exposed to the browserify moduleInitializer
    // https://github.com/browserify/browser-pack/blob/cd0bd31f8c110e19a80429019b64e887b1a82b2b/prelude.js#L38
    // browserify's browser-resolve uses "arguments[4]" to do direct module initializations
    // browserify seems to do this when module references are redirected by the "browser" field
    // this proxy shims this behavior
    // this is utilized by browserify's dedupe feature
    // though in the original browser-pack prelude it has a side effect that it is re-instantiated from the original module (no shared closure state)
    const directModuleInstantiationInterface = new Proxy({}, {
      get (_, targetModuleId) {
        const fakeModuleDefinition = [fakeModuleInitializer]
        return fakeModuleDefinition

        function fakeModuleInitializer () {
          const targetModuleExports = requireRelativeWithContext(targetModuleId)
          moduleObj.exports = targetModuleExports
        }
      }
    })

    return [require, module, exports, null, directModuleInstantiationInterface]
  }

})()
;
LavaMoat.loadBundle({1:{ id: 1, package: "cross-fetch", packageVersion: undefined, file: "/www/node_modules/cross-fetch/dist/browser-ponyfill.js", deps: {}, source: "(function () {\n  // source: ${filename}\n  return function (require, module, exports) {\nvar global = typeof self !== 'undefined' ? self : this;\nvar __self__ = (function () {\nfunction F() {\nthis.fetch = false;\nthis.DOMException = global.DOMException\n}\nF.prototype = global;\nreturn new F();\n})();\n(function(self) {\n\nvar irrelevant = (function (exports) {\n\n  var support = {\n    searchParams: 'URLSearchParams' in self,\n    iterable: 'Symbol' in self && 'iterator' in Symbol,\n    blob:\n      'FileReader' in self &&\n      'Blob' in self &&\n      (function() {\n        try {\n          new Blob();\n          return true\n        } catch (e) {\n          return false\n        }\n      })(),\n    formData: 'FormData' in self,\n    arrayBuffer: 'ArrayBuffer' in self\n  };\n\n  function isDataView(obj) {\n    return obj && DataView.prototype.isPrototypeOf(obj)\n  }\n\n  if (support.arrayBuffer) {\n    var viewClasses = [\n      '[object Int8Array]',\n      '[object Uint8Array]',\n      '[object Uint8ClampedArray]',\n      '[object Int16Array]',\n      '[object Uint16Array]',\n      '[object Int32Array]',\n      '[object Uint32Array]',\n      '[object Float32Array]',\n      '[object Float64Array]'\n    ];\n\n    var isArrayBufferView =\n      ArrayBuffer.isView ||\n      function(obj) {\n        return obj && viewClasses.indexOf(Object.prototype.toString.call(obj)) > -1\n      };\n  }\n\n  function normalizeName(name) {\n    if (typeof name !== 'string') {\n      name = String(name);\n    }\n    if (/[^a-z0-9\\-#$%&'*+.^_`|~]/i.test(name)) {\n      throw new TypeError('Invalid character in header field name')\n    }\n    return name.toLowerCase()\n  }\n\n  function normalizeValue(value) {\n    if (typeof value !== 'string') {\n      value = String(value);\n    }\n    return value\n  }\n\n  // Build a destructive iterator for the value list\n  function iteratorFor(items) {\n    var iterator = {\n      next: function() {\n        var value = items.shift();\n        return {done: value === undefined, value: value}\n      }\n    };\n\n    if (support.iterable) {\n      iterator[Symbol.iterator] = function() {\n        return iterator\n      };\n    }\n\n    return iterator\n  }\n\n  function Headers(headers) {\n    this.map = {};\n\n    if (headers instanceof Headers) {\n      headers.forEach(function(value, name) {\n        this.append(name, value);\n      }, this);\n    } else if (Array.isArray(headers)) {\n      headers.forEach(function(header) {\n        this.append(header[0], header[1]);\n      }, this);\n    } else if (headers) {\n      Object.getOwnPropertyNames(headers).forEach(function(name) {\n        this.append(name, headers[name]);\n      }, this);\n    }\n  }\n\n  Headers.prototype.append = function(name, value) {\n    name = normalizeName(name);\n    value = normalizeValue(value);\n    var oldValue = this.map[name];\n    this.map[name] = oldValue ? oldValue + ', ' + value : value;\n  };\n\n  Headers.prototype['delete'] = function(name) {\n    delete this.map[normalizeName(name)];\n  };\n\n  Headers.prototype.get = function(name) {\n    name = normalizeName(name);\n    return this.has(name) ? this.map[name] : null\n  };\n\n  Headers.prototype.has = function(name) {\n    return this.map.hasOwnProperty(normalizeName(name))\n  };\n\n  Headers.prototype.set = function(name, value) {\n    this.map[normalizeName(name)] = normalizeValue(value);\n  };\n\n  Headers.prototype.forEach = function(callback, thisArg) {\n    for (var name in this.map) {\n      if (this.map.hasOwnProperty(name)) {\n        callback.call(thisArg, this.map[name], name, this);\n      }\n    }\n  };\n\n  Headers.prototype.keys = function() {\n    var items = [];\n    this.forEach(function(value, name) {\n      items.push(name);\n    });\n    return iteratorFor(items)\n  };\n\n  Headers.prototype.values = function() {\n    var items = [];\n    this.forEach(function(value) {\n      items.push(value);\n    });\n    return iteratorFor(items)\n  };\n\n  Headers.prototype.entries = function() {\n    var items = [];\n    this.forEach(function(value, name) {\n      items.push([name, value]);\n    });\n    return iteratorFor(items)\n  };\n\n  if (support.iterable) {\n    Headers.prototype[Symbol.iterator] = Headers.prototype.entries;\n  }\n\n  function consumed(body) {\n    if (body.bodyUsed) {\n      return Promise.reject(new TypeError('Already read'))\n    }\n    body.bodyUsed = true;\n  }\n\n  function fileReaderReady(reader) {\n    return new Promise(function(resolve, reject) {\n      reader.onload = function() {\n        resolve(reader.result);\n      };\n      reader.onerror = function() {\n        reject(reader.error);\n      };\n    })\n  }\n\n  function readBlobAsArrayBuffer(blob) {\n    var reader = new FileReader();\n    var promise = fileReaderReady(reader);\n    reader.readAsArrayBuffer(blob);\n    return promise\n  }\n\n  function readBlobAsText(blob) {\n    var reader = new FileReader();\n    var promise = fileReaderReady(reader);\n    reader.readAsText(blob);\n    return promise\n  }\n\n  function readArrayBufferAsText(buf) {\n    var view = new Uint8Array(buf);\n    var chars = new Array(view.length);\n\n    for (var i = 0; i < view.length; i++) {\n      chars[i] = String.fromCharCode(view[i]);\n    }\n    return chars.join('')\n  }\n\n  function bufferClone(buf) {\n    if (buf.slice) {\n      return buf.slice(0)\n    } else {\n      var view = new Uint8Array(buf.byteLength);\n      view.set(new Uint8Array(buf));\n      return view.buffer\n    }\n  }\n\n  function Body() {\n    this.bodyUsed = false;\n\n    this._initBody = function(body) {\n      this._bodyInit = body;\n      if (!body) {\n        this._bodyText = '';\n      } else if (typeof body === 'string') {\n        this._bodyText = body;\n      } else if (support.blob && Blob.prototype.isPrototypeOf(body)) {\n        this._bodyBlob = body;\n      } else if (support.formData && FormData.prototype.isPrototypeOf(body)) {\n        this._bodyFormData = body;\n      } else if (support.searchParams && URLSearchParams.prototype.isPrototypeOf(body)) {\n        this._bodyText = body.toString();\n      } else if (support.arrayBuffer && support.blob && isDataView(body)) {\n        this._bodyArrayBuffer = bufferClone(body.buffer);\n        // IE 10-11 can't handle a DataView body.\n        this._bodyInit = new Blob([this._bodyArrayBuffer]);\n      } else if (support.arrayBuffer && (ArrayBuffer.prototype.isPrototypeOf(body) || isArrayBufferView(body))) {\n        this._bodyArrayBuffer = bufferClone(body);\n      } else {\n        this._bodyText = body = Object.prototype.toString.call(body);\n      }\n\n      if (!this.headers.get('content-type')) {\n        if (typeof body === 'string') {\n          this.headers.set('content-type', 'text/plain;charset=UTF-8');\n        } else if (this._bodyBlob && this._bodyBlob.type) {\n          this.headers.set('content-type', this._bodyBlob.type);\n        } else if (support.searchParams && URLSearchParams.prototype.isPrototypeOf(body)) {\n          this.headers.set('content-type', 'application/x-www-form-urlencoded;charset=UTF-8');\n        }\n      }\n    };\n\n    if (support.blob) {\n      this.blob = function() {\n        var rejected = consumed(this);\n        if (rejected) {\n          return rejected\n        }\n\n        if (this._bodyBlob) {\n          return Promise.resolve(this._bodyBlob)\n        } else if (this._bodyArrayBuffer) {\n          return Promise.resolve(new Blob([this._bodyArrayBuffer]))\n        } else if (this._bodyFormData) {\n          throw new Error('could not read FormData body as blob')\n        } else {\n          return Promise.resolve(new Blob([this._bodyText]))\n        }\n      };\n\n      this.arrayBuffer = function() {\n        if (this._bodyArrayBuffer) {\n          return consumed(this) || Promise.resolve(this._bodyArrayBuffer)\n        } else {\n          return this.blob().then(readBlobAsArrayBuffer)\n        }\n      };\n    }\n\n    this.text = function() {\n      var rejected = consumed(this);\n      if (rejected) {\n        return rejected\n      }\n\n      if (this._bodyBlob) {\n        return readBlobAsText(this._bodyBlob)\n      } else if (this._bodyArrayBuffer) {\n        return Promise.resolve(readArrayBufferAsText(this._bodyArrayBuffer))\n      } else if (this._bodyFormData) {\n        throw new Error('could not read FormData body as text')\n      } else {\n        return Promise.resolve(this._bodyText)\n      }\n    };\n\n    if (support.formData) {\n      this.formData = function() {\n        return this.text().then(decode)\n      };\n    }\n\n    this.json = function() {\n      return this.text().then(JSON.parse)\n    };\n\n    return this\n  }\n\n  // HTTP methods whose capitalization should be normalized\n  var methods = ['DELETE', 'GET', 'HEAD', 'OPTIONS', 'POST', 'PUT'];\n\n  function normalizeMethod(method) {\n    var upcased = method.toUpperCase();\n    return methods.indexOf(upcased) > -1 ? upcased : method\n  }\n\n  function Request(input, options) {\n    options = options || {};\n    var body = options.body;\n\n    if (input instanceof Request) {\n      if (input.bodyUsed) {\n        throw new TypeError('Already read')\n      }\n      this.url = input.url;\n      this.credentials = input.credentials;\n      if (!options.headers) {\n        this.headers = new Headers(input.headers);\n      }\n      this.method = input.method;\n      this.mode = input.mode;\n      this.signal = input.signal;\n      if (!body && input._bodyInit != null) {\n        body = input._bodyInit;\n        input.bodyUsed = true;\n      }\n    } else {\n      this.url = String(input);\n    }\n\n    this.credentials = options.credentials || this.credentials || 'same-origin';\n    if (options.headers || !this.headers) {\n      this.headers = new Headers(options.headers);\n    }\n    this.method = normalizeMethod(options.method || this.method || 'GET');\n    this.mode = options.mode || this.mode || null;\n    this.signal = options.signal || this.signal;\n    this.referrer = null;\n\n    if ((this.method === 'GET' || this.method === 'HEAD') && body) {\n      throw new TypeError('Body not allowed for GET or HEAD requests')\n    }\n    this._initBody(body);\n  }\n\n  Request.prototype.clone = function() {\n    return new Request(this, {body: this._bodyInit})\n  };\n\n  function decode(body) {\n    var form = new FormData();\n    body\n      .trim()\n      .split('&')\n      .forEach(function(bytes) {\n        if (bytes) {\n          var split = bytes.split('=');\n          var name = split.shift().replace(/\\+/g, ' ');\n          var value = split.join('=').replace(/\\+/g, ' ');\n          form.append(decodeURIComponent(name), decodeURIComponent(value));\n        }\n      });\n    return form\n  }\n\n  function parseHeaders(rawHeaders) {\n    var headers = new Headers();\n    // Replace instances of \\r\\n and \\n followed by at least one space or horizontal tab with a space\n    // https://tools.ietf.org/html/rfc7230#section-3.2\n    var preProcessedHeaders = rawHeaders.replace(/\\r?\\n[\\t ]+/g, ' ');\n    preProcessedHeaders.split(/\\r?\\n/).forEach(function(line) {\n      var parts = line.split(':');\n      var key = parts.shift().trim();\n      if (key) {\n        var value = parts.join(':').trim();\n        headers.append(key, value);\n      }\n    });\n    return headers\n  }\n\n  Body.call(Request.prototype);\n\n  function Response(bodyInit, options) {\n    if (!options) {\n      options = {};\n    }\n\n    this.type = 'default';\n    this.status = options.status === undefined ? 200 : options.status;\n    this.ok = this.status >= 200 && this.status < 300;\n    this.statusText = 'statusText' in options ? options.statusText : 'OK';\n    this.headers = new Headers(options.headers);\n    this.url = options.url || '';\n    this._initBody(bodyInit);\n  }\n\n  Body.call(Response.prototype);\n\n  Response.prototype.clone = function() {\n    return new Response(this._bodyInit, {\n      status: this.status,\n      statusText: this.statusText,\n      headers: new Headers(this.headers),\n      url: this.url\n    })\n  };\n\n  Response.error = function() {\n    var response = new Response(null, {status: 0, statusText: ''});\n    response.type = 'error';\n    return response\n  };\n\n  var redirectStatuses = [301, 302, 303, 307, 308];\n\n  Response.redirect = function(url, status) {\n    if (redirectStatuses.indexOf(status) === -1) {\n      throw new RangeError('Invalid status code')\n    }\n\n    return new Response(null, {status: status, headers: {location: url}})\n  };\n\n  exports.DOMException = self.DOMException;\n  try {\n    new exports.DOMException();\n  } catch (err) {\n    exports.DOMException = function(message, name) {\n      this.message = message;\n      this.name = name;\n      var error = Error(message);\n      this.stack = error.stack;\n    };\n    exports.DOMException.prototype = Object.create(Error.prototype);\n    exports.DOMException.prototype.constructor = exports.DOMException;\n  }\n\n  function fetch(input, init) {\n    return new Promise(function(resolve, reject) {\n      var request = new Request(input, init);\n\n      if (request.signal && request.signal.aborted) {\n        return reject(new exports.DOMException('Aborted', 'AbortError'))\n      }\n\n      var xhr = new XMLHttpRequest();\n\n      function abortXhr() {\n        xhr.abort();\n      }\n\n      xhr.onload = function() {\n        var options = {\n          status: xhr.status,\n          statusText: xhr.statusText,\n          headers: parseHeaders(xhr.getAllResponseHeaders() || '')\n        };\n        options.url = 'responseURL' in xhr ? xhr.responseURL : options.headers.get('X-Request-URL');\n        var body = 'response' in xhr ? xhr.response : xhr.responseText;\n        resolve(new Response(body, options));\n      };\n\n      xhr.onerror = function() {\n        reject(new TypeError('Network request failed'));\n      };\n\n      xhr.ontimeout = function() {\n        reject(new TypeError('Network request failed'));\n      };\n\n      xhr.onabort = function() {\n        reject(new exports.DOMException('Aborted', 'AbortError'));\n      };\n\n      xhr.open(request.method, request.url, true);\n\n      if (request.credentials === 'include') {\n        xhr.withCredentials = true;\n      } else if (request.credentials === 'omit') {\n        xhr.withCredentials = false;\n      }\n\n      if ('responseType' in xhr && support.blob) {\n        xhr.responseType = 'blob';\n      }\n\n      request.headers.forEach(function(value, name) {\n        xhr.setRequestHeader(name, value);\n      });\n\n      if (request.signal) {\n        request.signal.addEventListener('abort', abortXhr);\n\n        xhr.onreadystatechange = function() {\n          // DONE (success or failure)\n          if (xhr.readyState === 4) {\n            request.signal.removeEventListener('abort', abortXhr);\n          }\n        };\n      }\n\n      xhr.send(typeof request._bodyInit === 'undefined' ? null : request._bodyInit);\n    })\n  }\n\n  fetch.polyfill = true;\n\n  if (!self.fetch) {\n    self.fetch = fetch;\n    self.Headers = Headers;\n    self.Request = Request;\n    self.Response = Response;\n  }\n\n  exports.Headers = Headers;\n  exports.Request = Request;\n  exports.Response = Response;\n  exports.fetch = fetch;\n\n  Object.defineProperty(exports, '__esModule', { value: true });\n\n  return exports;\n\n}({}));\n})(__self__);\n__self__.fetch.ponyfill = true;\n// Remove \"polyfill\" property added by whatwg-fetch\ndelete __self__.fetch.polyfill;\n// Choose between native implementation (global) or custom implementation (__self__)\n// var ctx = global.fetch ? global : __self__;\nvar ctx = __self__; // this line disable service worker support temporarily\nexports = ctx.fetch // To enable: import fetch from 'cross-fetch'\nexports.default = ctx.fetch // For TypeScript consumers without esModuleInterop.\nexports.fetch = ctx.fetch // To enable: import {fetch} from 'cross-fetch'\nexports.Headers = ctx.Headers\nexports.Request = ctx.Request\nexports.Response = ctx.Response\nmodule.exports = exports\n\n  }\n}).call(this)",},2:{ id: 2, package: "eth-query", packageVersion: undefined, file: "/www/node_modules/eth-query/index.js", deps: {"json-rpc-random-id":4,"xtend":5}, source: "(function () {\n  // source: ${filename}\n  return function (require, module, exports) {\nconst extend = require('xtend')\nconst createRandomId = require('json-rpc-random-id')()\n\nmodule.exports = EthQuery\n\n\nfunction EthQuery(provider){\n  const self = this\n  self.currentProvider = provider\n}\n\n//\n// base queries\n//\n\n// default block\nEthQuery.prototype.getBalance =                          generateFnWithDefaultBlockFor(2, 'eth_getBalance')\nEthQuery.prototype.getCode =                             generateFnWithDefaultBlockFor(2, 'eth_getCode')\nEthQuery.prototype.getTransactionCount =                 generateFnWithDefaultBlockFor(2, 'eth_getTransactionCount')\nEthQuery.prototype.getStorageAt =                        generateFnWithDefaultBlockFor(3, 'eth_getStorageAt')\nEthQuery.prototype.call =                                generateFnWithDefaultBlockFor(2, 'eth_call')\n// standard\nEthQuery.prototype.protocolVersion =                     generateFnFor('eth_protocolVersion')\nEthQuery.prototype.syncing =                             generateFnFor('eth_syncing')\nEthQuery.prototype.coinbase =                            generateFnFor('eth_coinbase')\nEthQuery.prototype.mining =                              generateFnFor('eth_mining')\nEthQuery.prototype.hashrate =                            generateFnFor('eth_hashrate')\nEthQuery.prototype.gasPrice =                            generateFnFor('eth_gasPrice')\nEthQuery.prototype.accounts =                            generateFnFor('eth_accounts')\nEthQuery.prototype.blockNumber =                         generateFnFor('eth_blockNumber')\nEthQuery.prototype.getBlockTransactionCountByHash =      generateFnFor('eth_getBlockTransactionCountByHash')\nEthQuery.prototype.getBlockTransactionCountByNumber =    generateFnFor('eth_getBlockTransactionCountByNumber')\nEthQuery.prototype.getUncleCountByBlockHash =            generateFnFor('eth_getUncleCountByBlockHash')\nEthQuery.prototype.getUncleCountByBlockNumber =          generateFnFor('eth_getUncleCountByBlockNumber')\nEthQuery.prototype.sign =                                generateFnFor('eth_sign')\nEthQuery.prototype.sendTransaction =                     generateFnFor('eth_sendTransaction')\nEthQuery.prototype.sendRawTransaction =                  generateFnFor('eth_sendRawTransaction')\nEthQuery.prototype.estimateGas =                         generateFnFor('eth_estimateGas')\nEthQuery.prototype.getBlockByHash =                      generateFnFor('eth_getBlockByHash')\nEthQuery.prototype.getBlockByNumber =                    generateFnFor('eth_getBlockByNumber')\nEthQuery.prototype.getTransactionByHash =                generateFnFor('eth_getTransactionByHash')\nEthQuery.prototype.getTransactionByBlockHashAndIndex =   generateFnFor('eth_getTransactionByBlockHashAndIndex')\nEthQuery.prototype.getTransactionByBlockNumberAndIndex = generateFnFor('eth_getTransactionByBlockNumberAndIndex')\nEthQuery.prototype.getTransactionReceipt =               generateFnFor('eth_getTransactionReceipt')\nEthQuery.prototype.getUncleByBlockHashAndIndex =         generateFnFor('eth_getUncleByBlockHashAndIndex')\nEthQuery.prototype.getUncleByBlockNumberAndIndex =       generateFnFor('eth_getUncleByBlockNumberAndIndex')\nEthQuery.prototype.getCompilers =                        generateFnFor('eth_getCompilers')\nEthQuery.prototype.compileLLL =                          generateFnFor('eth_compileLLL')\nEthQuery.prototype.compileSolidity =                     generateFnFor('eth_compileSolidity')\nEthQuery.prototype.compileSerpent =                      generateFnFor('eth_compileSerpent')\nEthQuery.prototype.newFilter =                           generateFnFor('eth_newFilter')\nEthQuery.prototype.newBlockFilter =                      generateFnFor('eth_newBlockFilter')\nEthQuery.prototype.newPendingTransactionFilter =         generateFnFor('eth_newPendingTransactionFilter')\nEthQuery.prototype.uninstallFilter =                     generateFnFor('eth_uninstallFilter')\nEthQuery.prototype.getFilterChanges =                    generateFnFor('eth_getFilterChanges')\nEthQuery.prototype.getFilterLogs =                       generateFnFor('eth_getFilterLogs')\nEthQuery.prototype.getLogs =                             generateFnFor('eth_getLogs')\nEthQuery.prototype.getWork =                             generateFnFor('eth_getWork')\nEthQuery.prototype.submitWork =                          generateFnFor('eth_submitWork')\nEthQuery.prototype.submitHashrate =                      generateFnFor('eth_submitHashrate')\n\n// network level\n\nEthQuery.prototype.sendAsync = function(opts, cb){\n  const self = this\n  self.currentProvider.sendAsync(createPayload(opts), function(err, response){\n    if (!err && response.error) err = new Error('EthQuery - RPC Error - '+response.error.message)\n    if (err) return cb(err)\n    cb(null, response.result)\n  })\n}\n\n// util\n\nfunction generateFnFor(methodName){\n  return function(){\n    const self = this\n    var args = [].slice.call(arguments)\n    var cb = args.pop()\n    self.sendAsync({\n      method: methodName,\n      params: args,\n    }, cb)\n  }\n}\n\nfunction generateFnWithDefaultBlockFor(argCount, methodName){\n  return function(){\n    const self = this\n    var args = [].slice.call(arguments)\n    var cb = args.pop()\n    // set optional default block param\n    if (args.length < argCount) args.push('latest')\n    self.sendAsync({\n      method: methodName,\n      params: args,\n    }, cb)\n  }\n}\n\nfunction createPayload(data){\n  return extend({\n    // defaults\n    id: createRandomId(),\n    jsonrpc: '2.0',\n    params: [],\n    // user-specified\n  }, data)\n}\n\n  }\n}).call(this)",},3:{ id: 3, package: "h", packageVersion: undefined, file: "/www/node_modules/h/index.js", deps: {}, source: "(function () {\n  // source: ${filename}\n  return function (require, module, exports) {\n;(function () {\n\nfunction h() {\n  var args = [].slice.call(arguments), e = null\n  function item (l) {\n    \n    function parseClass (string) {\n      var m = string.split(/([\\.#]?[a-zA-Z0-9_-]+)/)\n      m.forEach(function (v) {\n        var s = v.substring(1,v.length)\n        if(!v) return \n        if(!e)\n          e = document.createElement(v)\n        else if (v[0] === '.')\n          e.classList.add(s)\n        else if (v[0] === '#')\n          e.setAttribute('id', s)\n        \n      })\n    }\n\n    if(l == null)\n      ;\n    else if('string' === typeof l) {\n      if(!e)\n        parseClass(l)\n      else\n        e.appendChild(document.createTextNode(l))\n    }\n    else if('number' === typeof l \n      || 'boolean' === typeof l\n      || l instanceof Date \n      || l instanceof RegExp ) {\n        e.appendChild(document.createTextNode(l.toString()))\n    }\n    else if (Array.isArray(l))\n      l.forEach(item)\n    else if(l instanceof HTMLElement)\n      e.appendChild(l)\n    else if ('object' === typeof l) {\n      for (var k in l) {\n        if('function' === typeof l[k])\n          e.addEventListener(k, l[k])\n        else if(k === 'style') {\n          for (var s in l[k])\n            e.style.setProperty(s, l[k][s])\n        }\n        else\n          e.setAttribute(k, l[k])\n      }\n    }\n  }\n  while(args.length) {\n    item(args.shift())\n  }\n  return e\n}\n\nif(typeof module === 'object')\n  module.exports = h\nelse\n  this.h = h\n})()\n\n  }\n}).call(this)",},4:{ id: 4, package: "json-rpc-random-id", packageVersion: undefined, file: "/www/node_modules/json-rpc-random-id/index.js", deps: {}, source: "(function () {\n  // source: ${filename}\n  return function (require, module, exports) {\nmodule.exports = IdIterator\n\nfunction IdIterator(opts){\n  opts = opts || {}\n  var max = opts.max || Number.MAX_SAFE_INTEGER\n  var idCounter = typeof opts.start !== 'undefined' ? opts.start : Math.floor(Math.random() * max)\n\n  return function createRandomId () {\n    idCounter = idCounter % max\n    return idCounter++\n  }\n\n}\n  }\n}).call(this)",},5:{ id: 5, package: "xtend", packageVersion: undefined, file: "/www/node_modules/xtend/immutable.js", deps: {}, source: "(function () {\n  // source: ${filename}\n  return function (require, module, exports) {\nmodule.exports = extend\n\nvar hasOwnProperty = Object.prototype.hasOwnProperty;\n\nfunction extend() {\n    var target = {}\n\n    for (var i = 0; i < arguments.length; i++) {\n        var source = arguments[i]\n\n        for (var key in source) {\n            if (hasOwnProperty.call(source, key)) {\n                target[key] = source[key]\n            }\n        }\n    }\n\n    return target\n}\n\n  }\n}).call(this)",},6:{ id: 6, package: "<root>", packageVersion: undefined, file: "/www/src/webapp/index.js", deps: {"cross-fetch":1,"eth-query":2,"h":3}, source: "(function () {\n  // source: ${filename}\n  return function (require, module, exports) {\nconst h = require('h')\nconst fetch = require('cross-fetch');\nconst EthQuery = require('eth-query')\n\nvar state = {\n  isLoading: true,\n\n  // injected at build time\n  faucetAddress: \"0x81b7e08f65bdf5648606c89998a9cc8164397647\",\n  faucetBalance: null,\n\n  userAddress: null,\n  fromBalance: null,\n  errorMessage: null,\n\n  transactions: []\n}\n\nwindow.addEventListener('load', startApp)\n\nfunction startApp () {\n\n  // attempt to get provider from environment\n  let provider\n  if (global.ethereum) {\n    provider = global.ethereum\n  } else if (global.web3) {\n    provider = global.web3.currentProvider\n  }\n\n  // display warning if incompatible\n  if (!provider) {\n    // abort\n    render(h('span', 'No ethereum provider detected. Install a web-enabled wallet (eg MetaMask metamask.io) to continue'))\n    return\n  }\n\n  // create query helper\n  global.ethQuery = new EthQuery(provider)\n  global.provider = provider\n\n  renderApp()\n  updateStateFromNetwork()\n  setInterval(updateStateFromNetwork, 4000)\n}\n\nfunction updateStateFromNetwork () {\n  getNetwork()\n  getAccounts()\n  getBalances()\n  renderApp()\n}\n\nfunction getNetwork () {\n  global.provider.sendAsync({ id: 1, jsonrpc: '2.0', method: 'net_version' }, function (err, res) {\n    if (err) return console.error(err)\n    if (res.error) return console.res.error(res.error)\n    var network = res.result\n    state.network = network\n    renderApp()\n  })\n}\n\nfunction getAccounts () {\n  global.ethQuery.accounts(function (err, accounts) {\n    if (err) return console.error(err)\n    var address = accounts[0]\n    if (state.userAddress === address) return\n    state.userAddress = address\n    state.fromBalance = null\n    getBalances()\n    renderApp()\n  })\n}\n\n/*\n * The big new method added for EIP-1102 privacy mode compatibility.\n * Read more here:\n * https://medium.com/metamask/eip-1102-preparing-your-dapp-5027b2c9ed76\n */\nasync function requestAccounts () {\n  const provider = global.provider\n  if ('enable' in provider) {\n    try {\n      const accounts = await provider.enable()\n      getAccounts()\n      return accounts[0]\n    } catch (err) {\n      window.alert('Your web3 account is currently locked. Please unlock it to continue.')\n    }\n  } else {\n    // Fallback to old way if no privacy mode available\n    if (state.userAddress) {\n      return state.userAddress\n    } else {\n      window.alert('Your web3 account is currently locked. Please unlock it to continue.')\n      throw new Error('web3 account locked')\n    }\n  }\n}\n\nfunction getBalances () {\n  if (state.faucetAddress) {\n    global.ethQuery.getBalance(state.faucetAddress, function (err, result) {\n      if (err) return console.error(err)\n      state.faucetBalance = (parseInt(result, 16) / 1e18).toFixed(2)\n      renderApp()\n    })\n  }\n\n  if (state.userAddress) {\n    global.ethQuery.getBalance(state.userAddress, function (err, result) {\n      if (err) return console.error(err)\n      state.fromBalance = (parseInt(result, 16) / 1e18).toFixed(2)\n      renderApp()\n    })\n  }\n}\n\nfunction renderApp () {\n  // if (state.isLoading) {\n  //   return render(h('span', 'web3 detected - Loading...'))\n  // }\n\n  // render wrong network warning\n  if (state.network === '1') {\n    return render([\n\n      h('section.container', [\n        h('div.panel.panel-default', [\n          h('div.panel-heading', [\n            h('h3', 'network')\n          ]),\n          h('div.panel-body', [\n            'currently on mainnet - please select the correct test network'\n          ])\n        ])\n      ])\n\n    ])\n  }\n\n  // render faucet ui\n  render([\n\n    h('nav.navbar.navbar-default', [\n      h('h1.container-fluid', 'MetaMask Ether Faucet')\n    ]),\n\n    h('section.container', [\n\n      h('div.panel.panel-default', [\n        h('div.panel-heading', [\n          h('h3', 'faucet')\n        ]),\n        h('div.panel-body', [\n          h('div', 'address: ' + state.faucetAddress),\n          h('div', 'balance: ' + formatBalance(state.faucetBalance)),\n          h('button.btn.btn-success', 'request 1 ether from faucet', {\n            style: {\n              margin: '4px'\n            },\n            // disabled: state.userAddress ? null : true,\n            click: getEther\n          })\n        ])\n      ]),\n\n      h('div.panel.panel-default', [\n        h('div.panel-heading', [\n          h('h3', 'user')\n        ]),\n        h('div.panel-body', [\n          h('div', 'address: ' + state.userAddress),\n          h('div', 'balance: ' + formatBalance(state.fromBalance)),\n          h('div', 'donate to faucet:'),\n          h('button.btn.btn-warning', '1 ether', {\n            style: {\n              margin: '4px'\n            },\n            // disabled: state.userAddress ? null : true,\n            click: sendTx.bind(null, 1)\n          }),\n          h('button.btn.btn-warning', '10 ether', {\n            style: {\n              margin: '4px'\n            },\n            // disabled: state.userAddress ? null : true,\n            click: sendTx.bind(null, 10)\n          }),\n          h('button.btn.btn-warning', '100 ether', {\n            style: {\n              margin: '4px'\n            },\n            // disabled: state.userAddress ? null : true,\n            click: sendTx.bind(null, 100)\n          })\n        ])\n      ]),\n\n      h('div.panel.panel-default', [\n        h('div.panel-heading', [\n          h('h3', 'transactions')\n        ]),\n        h('div.panel-body', {\n          style: {\n            'flex-direction': 'column',\n            display: 'flex'\n          }\n        }, (\n          state.transactions.map((txHash) => {\n            return link(`https://ropsten.etherscan.io/tx/${txHash}`, txHash)\n          })\n        ))\n      ])\n\n    ]),\n\n    state.errorMessage ? h('div', { style: { color: 'red' } }, state.errorMessage) : null\n\n  ])\n}\n\nfunction link (url, content) {\n  return h('a', { href: url, target: '_blank' }, content)\n}\n\nasync function getEther () {\n  const account = await requestAccounts()\n\n  // We already prompted to unlock in requestAccounts()\n  if (!account) return\n\n  var uri = `${window.location.href}v0/request`\n  var data = account\n\n  let res, body, err\n  \n  try {\n    res = await fetch(uri, {\n      method: 'POST',\n      body: data,\n      headers: {\n        'Content-Type': 'application/rawdata'\n      }\n    })\n    body = await res.text()\n  } catch (error) {\n    err = error\n  }\n\n  // display error\n  if (err) {\n    state.errorMessage = err || err.stack\n    return\n  }\n\n  if (res.status === 420) {\n    state.errorMessage = `Being ratelimited... try again later`\n    return\n  }\n\n  if (!res.ok) {\n    state.errorMessage = `Error: ${res.status} ${res.statusText} ${body}`\n    return\n  }\n\n  // display error-in-body\n  try {\n    if (body.slice(0, 2) === '0x') {\n      state.transactions.push(body)\n      state.errorMessage = null\n    } else {\n      state.errorMessage = body\n    }\n  } catch (err) {\n    state.errorMessage = err || err.stack\n  }\n\n  // display tx hash\n  console.log('faucet response:', body)\n  updateStateFromNetwork()\n}\n\nasync function sendTx (value) {\n  const address = await requestAccounts()\n  if (!address) return\n\n  global.ethQuery.sendTransaction({\n    from: address,\n    to: state.faucetAddress,\n    value: '0x' + (value * 1e18).toString(16)\n  }, function (err, txHash) {\n    if (err) {\n      state.errorMessage = (err && err.stack)\n    } else {\n      console.log('user sent tx:', txHash)\n      state.errorMessage = null\n      state.transactions.push(txHash)\n    }\n    updateStateFromNetwork()\n  })\n}\n\nfunction render (elements) {\n  if (!Array.isArray(elements)) elements = [elements]\n  elements = elements.filter(Boolean)\n  // clear\n  document.body.innerHTML = ''\n  // insert\n  elements.forEach(function (element) {\n    document.body.appendChild(element)\n  })\n}\n\nfunction formatBalance (balance) {\n  return balance ? balance + ' ether' : '...'\n}\n\n  }\n}).call(this)",}},[6],{"resources":{"cross-fetch":{"globals":{"Blob":true,"FileReader":true,"FormData":true,"URLSearchParams.prototype.isPrototypeOf":true,"XMLHttpRequest":true}},"eth-query":{"packages":{"json-rpc-random-id":true,"xtend":true}},"h":{"globals":{"HTMLElement":true,"document.createElement":true,"document.createTextNode":true}},"process":{"globals":{"clearTimeout":true,"setTimeout":true}}}})
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJzb3VyY2VzIjpbIi4uLy4uL25vZGVfbW9kdWxlcy9sYXZhbW9hdC1icm93c2VyaWZ5L3NyYy9fcHJlbHVkZS5qcyJdLCJuYW1lcyI6W10sIm1hcHBpbmdzIjoiQUFBQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBIiwiZmlsZSI6ImdlbmVyYXRlZC5qcyIsInNvdXJjZVJvb3QiOiIiLCJzb3VyY2VzQ29udGVudCI6WyIvLyBMYXZhTW9hdCBQcmVsdWRlXG4oZnVuY3Rpb24oKSB7XG5cbiAgLy8gaWRlbnRpZnkgdGhlIGdsb2JhbFJlZlxuICBjb25zdCBnbG9iYWxSZWYgPSAodHlwZW9mIGdsb2JhbFRoaXMgIT09ICd1bmRlZmluZWQnKSA/IGdsb2JhbFRoaXMgOiAodHlwZW9mIHNlbGYgIT09ICd1bmRlZmluZWQnKSA/IHNlbGYgOiAodHlwZW9mIGdsb2JhbCAhPT0gJ3VuZGVmaW5lZCcpID8gZ2xvYmFsIDogdW5kZWZpbmVkXG4gIGlmICghZ2xvYmFsUmVmKSB7XG4gICAgdGhyb3cgbmV3IEVycm9yKCdMYXZhbW9hdCAtIHVuYWJsZSB0byBpZGVudGlmeSBnbG9iYWxSZWYnKVxuICB9XG5cbiAgLy8gY29uZmlnIGFuZCBidW5kbGUgbW9kdWxlIHN0b3JlXG4gIGNvbnN0IGxhdmFtb2F0Q29uZmlnID0geyByZXNvdXJjZXM6IHt9IH1cbiAgY29uc3QgbW9kdWxlcyA9IHt9XG5cbiAgLy8gaW5pdGlhbGl6ZSB0aGUga2VybmVsXG4gIGNvbnN0IGNyZWF0ZUtlcm5lbCA9IC8vIExhdmFNb2F0IFByZWx1ZGVcbihmdW5jdGlvbiAoKSB7XG4gIHJldHVybiBjcmVhdGVLZXJuZWxcblxuICBmdW5jdGlvbiBjcmVhdGVLZXJuZWwgKHtcbiAgICBsYXZhbW9hdENvbmZpZyxcbiAgICBsb2FkTW9kdWxlRGF0YSxcbiAgICBnZXRSZWxhdGl2ZU1vZHVsZUlkLFxuICAgIHByZXBhcmVNb2R1bGVJbml0aWFsaXplckFyZ3MsXG4gICAgZ2V0RXh0ZXJuYWxDb21wYXJ0bWVudCxcbiAgICBnbG9iYWxUaGlzUmVmcyxcbiAgfSkge1xuICAgIGNvbnN0IGRlYnVnTW9kZSA9IGZhbHNlXG5cbiAgICAvLyBpZGVudGlmeSB0aGUgZ2xvYmFsUmVmXG4gICAgY29uc3QgZ2xvYmFsUmVmID0gKHR5cGVvZiBnbG9iYWxUaGlzICE9PSAndW5kZWZpbmVkJykgPyBnbG9iYWxUaGlzIDogKHR5cGVvZiBzZWxmICE9PSAndW5kZWZpbmVkJykgPyBzZWxmIDogKHR5cGVvZiBnbG9iYWwgIT09ICd1bmRlZmluZWQnKSA/IGdsb2JhbCA6IHVuZGVmaW5lZFxuICAgIGlmICghZ2xvYmFsUmVmKSB7XG4gICAgICB0aHJvdyBuZXcgRXJyb3IoJ0xhdmFtb2F0IC0gdW5hYmxlIHRvIGlkZW50aWZ5IGdsb2JhbFJlZicpXG4gICAgfVxuXG4gICAgLy8gcG9seWZpbGwgZ2xvYmFsVGhpc1xuICAgIGlmIChnbG9iYWxSZWYgJiYgIWdsb2JhbFJlZi5nbG9iYWxUaGlzKSB7XG4gICAgICBnbG9iYWxSZWYuZ2xvYmFsVGhpcyA9IGdsb2JhbFJlZlxuICAgIH1cblxuICAgIC8vIGNyZWF0ZSB0aGUgU0VTIHJvb3RSZWFsbVxuICAgIC8vIFwidGVtcGxhdGVSZXF1aXJlXCIgY2FsbHMgYXJlIGlubGluZWQgaW4gXCJnZW5lcmF0ZVByZWx1ZGVcIlxuICAgIC8vIGxvYWQtYmVhcmluZyBzZW1pLWNvbG9uLCBkbyBub3QgcmVtb3ZlXG4gICAgOy8vIGRlZmluZSBzZXNcbihmdW5jdGlvbigpe1xuICBjb25zdCBnbG9iYWwgPSBnbG9iYWxSZWZcbiAgY29uc3QgZXhwb3J0cyA9IHt9XG4gIGNvbnN0IG1vZHVsZSA9IHsgZXhwb3J0cyB9XG4gIDsoZnVuY3Rpb24oKXtcbi8vIFNUQVJUIG9mIGluamVjdGVkIGNvZGUgZnJvbSBzZXNcbihmdW5jdGlvbiAoZmFjdG9yeSkge1xuICB0eXBlb2YgZGVmaW5lID09PSAnZnVuY3Rpb24nICYmIGRlZmluZS5hbWQgPyBkZWZpbmUoZmFjdG9yeSkgOlxuICBmYWN0b3J5KCk7XG59KChmdW5jdGlvbiAoKSB7ICd1c2Ugc3RyaWN0JztcblxuICAvKipcbiAgICogY29tbW9ucy5qc1xuICAgKiBEZWNsYXJlIHNob3J0aGFuZCBmdW5jdGlvbnMuIFNoYXJpbmcgdGhlc2UgZGVjbGFyYXRpb25zIGFjcm9zcyBtb2R1bGVzXG4gICAqIGltcHJvdmVzIG9uIGNvbnNpc3RlbmN5IGFuZCBtaW5pZmljYXRpb24uIFVudXNlZCBkZWNsYXJhdGlvbnMgYXJlXG4gICAqIGRyb3BwZWQgYnkgdGhlIHRyZWUgc2hha2luZyBwcm9jZXNzLlxuICAgKlxuICAgKiBXZSBjYXB0dXJlIHRoZXNlLCBub3QganVzdCBmb3IgYnJldml0eSwgYnV0IGZvciBzZWN1cml0eS4gSWYgYW55IGNvZGVcbiAgICogbW9kaWZpZXMgT2JqZWN0IHRvIGNoYW5nZSB3aGF0ICdhc3NpZ24nIHBvaW50cyB0bywgdGhlIENvbXBhcnRtZW50IHNoaW1cbiAgICogd291bGQgYmUgY29ycnVwdGVkLlxuICAgKi9cblxuICBjb25zdCB7XG4gICAgYXNzaWduLFxuICAgIGNyZWF0ZSxcbiAgICBkZWZpbmVQcm9wZXJ0aWVzLFxuICAgIGVudHJpZXMsXG4gICAgZnJlZXplLFxuICAgIGdldE93blByb3BlcnR5RGVzY3JpcHRvcixcbiAgICBnZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3JzLFxuICAgIGdldE93blByb3BlcnR5TmFtZXMsXG4gICAgZ2V0UHJvdG90eXBlT2YsXG4gICAgaXMsXG4gICAgaXNFeHRlbnNpYmxlLFxuICAgIGtleXMsXG4gICAgcHJvdG90eXBlOiBvYmplY3RQcm90b3R5cGUsXG4gICAgc2VhbCxcbiAgICBzZXRQcm90b3R5cGVPZixcbiAgICB2YWx1ZXMsXG4gIH0gPSBPYmplY3Q7XG5cbiAgLy8gQXQgdGltZSBvZiB0aGlzIHdyaXRpbmcsIHdlIHN0aWxsIHN1cHBvcnQgTm9kZSAxMCB3aGljaCBkb2Vzbid0IGhhdmVcbiAgLy8gYE9iamVjdC5mcm9tRW50cmllc2AuIElmIGl0IGlzIGFic2VudCwgdGhpcyBzaG91bGQgYmUgYW4gYWRlcXVhdGVcbiAgLy8gcmVwbGFjZW1lbnQuXG4gIC8vIEJ5IHRoZSB0ZXJtaW5vbG9neSBvZiBodHRwczovL3Bvbnlmb28uY29tL2FydGljbGVzL3BvbHlmaWxscy1vci1wb255ZmlsbHNcbiAgLy8gaXQgaXMgYSBwb255ZmlsbCByYXRoZXIgdGhhbiBhIHBvbHlmaWxsIG9yIHNoaW0gYmVjYXVzZSB3ZSBkbyBub3RcbiAgLy8gaW5zdGFsbCBpdCBvbiBgT2JqZWN0YC5cbiAgY29uc3Qgb2JqZWN0RnJvbUVudHJpZXMgPSBlbnRyeVBhaXJzID0+IHtcbiAgICBjb25zdCByZXN1bHQgPSB7fTtcbiAgICBmb3IgKGNvbnN0IFtwcm9wLCB2YWxdIG9mIGVudHJ5UGFpcnMpIHtcbiAgICAgIHJlc3VsdFtwcm9wXSA9IHZhbDtcbiAgICB9XG4gICAgcmV0dXJuIHJlc3VsdDtcbiAgfTtcblxuICBjb25zdCBmcm9tRW50cmllcyA9IE9iamVjdC5mcm9tRW50cmllcyB8fCBvYmplY3RGcm9tRW50cmllcztcblxuICBjb25zdCBkZWZpbmVQcm9wZXJ0eSA9IChvYmplY3QsIHByb3AsIGRlc2NyaXB0b3IpID0+IHtcbiAgICAvLyBPYmplY3QuZGVmaW5lUHJvcGVydHkgaXMgYWxsb3dlZCB0byBmYWlsIHNpbGVudGx5IHNvIHdlIHVzZVxuICAgIC8vIE9iamVjdC5kZWZpbmVQcm9wZXJ0aWVzIGluc3RlYWQuXG4gICAgcmV0dXJuIGRlZmluZVByb3BlcnRpZXMob2JqZWN0LCB7IFtwcm9wXTogZGVzY3JpcHRvciB9KTtcbiAgfTtcblxuICBjb25zdCB7IGFwcGx5LCBjb25zdHJ1Y3QsIGdldDogcmVmbGVjdEdldCwgc2V0OiByZWZsZWN0U2V0IH0gPSBSZWZsZWN0O1xuXG4gIGNvbnN0IHsgaXNBcnJheSwgcHJvdG90eXBlOiBhcnJheVByb3RvdHlwZSB9ID0gQXJyYXk7XG4gIGNvbnN0IHsgcmV2b2NhYmxlOiBwcm94eVJldm9jYWJsZSB9ID0gUHJveHk7XG4gIGNvbnN0IHsgcHJvdG90eXBlOiByZWdleHBQcm90b3R5cGUgfSA9IFJlZ0V4cDtcbiAgY29uc3QgeyBwcm90b3R5cGU6IHN0cmluZ1Byb3RvdHlwZSB9ID0gU3RyaW5nO1xuICBjb25zdCB7IHByb3RvdHlwZTogd2Vha21hcFByb3RvdHlwZSB9ID0gV2Vha01hcDtcblxuICAvKipcbiAgICogdW5jdXJyeVRoaXMoKVxuICAgKiBUaGlzIGZvcm0gb2YgdW5jdXJyeSB1c2VzIFJlZmxlY3QuYXBwbHkoKVxuICAgKlxuICAgKiBUaGUgb3JpZ2luYWwgdW5jdXJyeSB1c2VzOlxuICAgKiBjb25zdCBiaW5kID0gRnVuY3Rpb24ucHJvdG90eXBlLmJpbmQ7XG4gICAqIGNvbnN0IHVuY3VycnlUaGlzID0gYmluZC5iaW5kKGJpbmQuY2FsbCk7XG4gICAqXG4gICAqIFNlZSB0aG9zZSByZWZlcmVuY2UgZm9yIGEgY29tcGxldGUgZXhwbGFuYXRpb246XG4gICAqIGh0dHA6Ly93aWtpLmVjbWFzY3JpcHQub3JnL2Rva3UucGhwP2lkPWNvbnZlbnRpb25zOnNhZmVfbWV0YV9wcm9ncmFtbWluZ1xuICAgKiB3aGljaCBvbmx5IGxpdmVzIGF0XG4gICAqIGh0dHA6Ly93ZWIuYXJjaGl2ZS5vcmcvd2ViLzIwMTYwODA1MjI1NzEwL2h0dHA6Ly93aWtpLmVjbWFzY3JpcHQub3JnL2Rva3UucGhwP2lkPWNvbnZlbnRpb25zOnNhZmVfbWV0YV9wcm9ncmFtbWluZ1xuICAgKlxuICAgKiBAcGFyYW0geyh0aGlzQXJnOiBPYmplY3QsIC4uLmFyZ3M6IGFueVtdKSA9PiBhbnl9IGZuXG4gICAqL1xuICBjb25zdCB1bmN1cnJ5VGhpcyA9IGZuID0+ICh0aGlzQXJnLCAuLi5hcmdzKSA9PiBhcHBseShmbiwgdGhpc0FyZywgYXJncyk7XG5cbiAgY29uc3Qgb2JqZWN0SGFzT3duUHJvcGVydHkgPSB1bmN1cnJ5VGhpcyhvYmplY3RQcm90b3R5cGUuaGFzT3duUHJvcGVydHkpO1xuICAvL1xuICBjb25zdCBhcnJheUZpbHRlciA9IHVuY3VycnlUaGlzKGFycmF5UHJvdG90eXBlLmZpbHRlcik7XG4gIGNvbnN0IGFycmF5Sm9pbiA9IHVuY3VycnlUaGlzKGFycmF5UHJvdG90eXBlLmpvaW4pO1xuICBjb25zdCBhcnJheVB1c2ggPSB1bmN1cnJ5VGhpcyhhcnJheVByb3RvdHlwZS5wdXNoKTtcbiAgY29uc3QgYXJyYXlQb3AgPSB1bmN1cnJ5VGhpcyhhcnJheVByb3RvdHlwZS5wb3ApO1xuICBjb25zdCBhcnJheUluY2x1ZGVzID0gdW5jdXJyeVRoaXMoYXJyYXlQcm90b3R5cGUuaW5jbHVkZXMpO1xuICAvL1xuICBjb25zdCByZWdleHBUZXN0ID0gdW5jdXJyeVRoaXMocmVnZXhwUHJvdG90eXBlLnRlc3QpO1xuICAvL1xuICBjb25zdCBzdHJpbmdNYXRjaCA9IHVuY3VycnlUaGlzKHN0cmluZ1Byb3RvdHlwZS5tYXRjaCk7XG4gIGNvbnN0IHN0cmluZ1NlYXJjaCA9IHVuY3VycnlUaGlzKHN0cmluZ1Byb3RvdHlwZS5zZWFyY2gpO1xuICBjb25zdCBzdHJpbmdTbGljZSA9IHVuY3VycnlUaGlzKHN0cmluZ1Byb3RvdHlwZS5zbGljZSk7XG4gIGNvbnN0IHN0cmluZ1NwbGl0ID0gdW5jdXJyeVRoaXMoc3RyaW5nUHJvdG90eXBlLnNwbGl0KTtcbiAgLy9cbiAgY29uc3Qgd2Vha21hcEdldCA9IHVuY3VycnlUaGlzKHdlYWttYXBQcm90b3R5cGUuZ2V0KTtcbiAgY29uc3Qgd2Vha21hcFNldCA9IHVuY3VycnlUaGlzKHdlYWttYXBQcm90b3R5cGUuc2V0KTtcbiAgY29uc3Qgd2Vha21hcEhhcyA9IHVuY3VycnlUaGlzKHdlYWttYXBQcm90b3R5cGUuaGFzKTtcblxuICAvKipcbiAgICogaW1tdXRhYmxlT2JqZWN0XG4gICAqIEFuIGltbXV0YWJsZSAoZnJvemVuKSBleG90aWMgb2JqZWN0IGFuZCBpcyBzYWZlIHRvIHNoYXJlLlxuICAgKi9cbiAgY29uc3QgaW1tdXRhYmxlT2JqZWN0ID0gZnJlZXplKHsgX19wcm90b19fOiBudWxsIH0pO1xuXG4gIGNvbnN0IG5hdGl2ZVN1ZmZpeCA9ICcpIHsgW25hdGl2ZSBjb2RlXSB9JztcblxuICAvLyBOb3RlOiBUb3AgbGV2ZWwgbXV0YWJsZSBzdGF0ZS4gRG9lcyBub3QgbWFrZSBhbnl0aGluZyB3b3JzZSwgc2luY2UgdGhlXG4gIC8vIHBhdGNoaW5nIG9mIGBGdW5jdGlvbi5wcm90b3R5cGUudG9TdHJpbmdgIGlzIGFsc28gZ2xvYmFsbHkgc3RhdGVmdWwuIFdlXG4gIC8vIHVzZSB0aGlzIHRvcCBsZXZlbCBzdGF0ZSBzbyB0aGF0IG11bHRpcGxlIGNhbGxzIHRvIGB0YW1lRnVuY3Rpb25Ub1N0cmluZ2AgYXJlXG4gIC8vIGlkZW1wb3RlbnQsIHJhdGhlciB0aGFuIGNyZWF0aW5nIHJlZHVuZGFudCBpbmRpcmVjdGlvbnMuXG4gIGxldCBuYXRpdmVCcmFuZGVyO1xuXG4gIC8qKlxuICAgKiBSZXBsYWNlIGBGdW5jdGlvbi5wcm90b3R5cGUudG9TdHJpbmdgIHdpdGggb25lIHRoYXQgcmVjb2duaXplc1xuICAgKiBzaGltbWVkIGZ1bmN0aW9ucyBhcyBob25vcmFyeSBuYXRpdmUgZnVuY3Rpb25zLlxuICAgKi9cbiAgZnVuY3Rpb24gdGFtZUZ1bmN0aW9uVG9TdHJpbmcoKSB7XG4gICAgaWYgKG5hdGl2ZUJyYW5kZXIgPT09IHVuZGVmaW5lZCkge1xuICAgICAgY29uc3QgbmF0aXZlQnJhbmQgPSBuZXcgV2Vha1NldCgpO1xuXG4gICAgICBjb25zdCBvcmlnaW5hbEZ1bmN0aW9uVG9TdHJpbmcgPSBGdW5jdGlvbi5wcm90b3R5cGUudG9TdHJpbmc7XG5cbiAgICAgIGNvbnN0IHRhbWluZ01ldGhvZHMgPSB7XG4gICAgICAgIHRvU3RyaW5nKCkge1xuICAgICAgICAgIGNvbnN0IHN0ciA9IGFwcGx5KG9yaWdpbmFsRnVuY3Rpb25Ub1N0cmluZywgdGhpcywgW10pO1xuICAgICAgICAgIGlmIChzdHIuZW5kc1dpdGgobmF0aXZlU3VmZml4KSB8fCAhbmF0aXZlQnJhbmQuaGFzKHRoaXMpKSB7XG4gICAgICAgICAgICByZXR1cm4gc3RyO1xuICAgICAgICAgIH1cbiAgICAgICAgICByZXR1cm4gYGZ1bmN0aW9uICR7dGhpcy5uYW1lfSgpIHsgW25hdGl2ZSBjb2RlXSB9YDtcbiAgICAgICAgfSxcbiAgICAgIH07XG5cbiAgICAgIGRlZmluZVByb3BlcnR5KEZ1bmN0aW9uLnByb3RvdHlwZSwgJ3RvU3RyaW5nJywge1xuICAgICAgICB2YWx1ZTogdGFtaW5nTWV0aG9kcy50b1N0cmluZyxcbiAgICAgIH0pO1xuXG4gICAgICBuYXRpdmVCcmFuZGVyID0gZnJlZXplKGZ1bmMgPT4gbmF0aXZlQnJhbmQuYWRkKGZ1bmMpKTtcbiAgICB9XG4gICAgcmV0dXJuIG5hdGl2ZUJyYW5kZXI7XG4gIH1cblxuICAvKipcbiAgICogQGZpbGUgRXhwb3J0cyB7QGNvZGUgd2hpdGVsaXN0fSwgYSByZWN1cnNpdmVseSBkZWZpbmVkXG4gICAqIEpTT04gcmVjb3JkIGVudW1lcmF0aW5nIGFsbCBpbnRyaW5zaWNzIGFuZCB0aGVpciBwcm9wZXJ0aWVzXG4gICAqIGFjY29yZGluZyB0byBFQ01BIHNwZWNzLlxuICAgKlxuICAgKiBAYXV0aG9yIEpGIFBhcmFkaXNcbiAgICogQGF1dGhvciBNYXJrIFMuIE1pbGxlclxuICAgKi9cblxuICAvKiBlc2xpbnQgbWF4LWxpbmVzOiAwICovXG5cbiAgLyoqXG4gICAqIGNvbnN0YW50UHJvcGVydGllc1xuICAgKiBub24tY29uZmlndXJhYmxlLCBub24td3JpdGFibGUgZGF0YSBwcm9wZXJ0aWVzIG9mIGFsbCBnbG9iYWwgb2JqZWN0cy5cbiAgICogTXVzdCBiZSBwb3dlcmxlc3MuXG4gICAqIE1hcHMgZnJvbSBwcm9wZXJ0eSBuYW1lIHRvIHRoZSBhY3R1YWwgdmFsdWVcbiAgICovXG4gIGNvbnN0IGNvbnN0YW50UHJvcGVydGllcyA9IHtcbiAgICAvLyAqKiogVmFsdWUgUHJvcGVydGllcyBvZiB0aGUgR2xvYmFsIE9iamVjdFxuXG4gICAgSW5maW5pdHksXG4gICAgTmFOLFxuICAgIHVuZGVmaW5lZCxcbiAgfTtcblxuICAvKipcbiAgICogdW5pdmVyc2FsUHJvcGVydHlOYW1lc1xuICAgKiBQcm9wZXJ0aWVzIG9mIGFsbCBnbG9iYWwgb2JqZWN0cy5cbiAgICogTXVzdCBiZSBwb3dlcmxlc3MuXG4gICAqIE1hcHMgZnJvbSBwcm9wZXJ0eSBuYW1lIHRvIHRoZSBpbnRyaW5zaWMgbmFtZSBpbiB0aGUgd2hpdGVsaXN0LlxuICAgKi9cbiAgY29uc3QgdW5pdmVyc2FsUHJvcGVydHlOYW1lcyA9IHtcbiAgICAvLyAqKiogRnVuY3Rpb24gUHJvcGVydGllcyBvZiB0aGUgR2xvYmFsIE9iamVjdFxuXG4gICAgaXNGaW5pdGU6ICdpc0Zpbml0ZScsXG4gICAgaXNOYU46ICdpc05hTicsXG4gICAgcGFyc2VGbG9hdDogJ3BhcnNlRmxvYXQnLFxuICAgIHBhcnNlSW50OiAncGFyc2VJbnQnLFxuXG4gICAgZGVjb2RlVVJJOiAnZGVjb2RlVVJJJyxcbiAgICBkZWNvZGVVUklDb21wb25lbnQ6ICdkZWNvZGVVUklDb21wb25lbnQnLFxuICAgIGVuY29kZVVSSTogJ2VuY29kZVVSSScsXG4gICAgZW5jb2RlVVJJQ29tcG9uZW50OiAnZW5jb2RlVVJJQ29tcG9uZW50JyxcblxuICAgIC8vICoqKiBDb25zdHJ1Y3RvciBQcm9wZXJ0aWVzIG9mIHRoZSBHbG9iYWwgT2JqZWN0XG5cbiAgICBBcnJheTogJ0FycmF5JyxcbiAgICBBcnJheUJ1ZmZlcjogJ0FycmF5QnVmZmVyJyxcbiAgICBCaWdJbnQ6ICdCaWdJbnQnLFxuICAgIEJpZ0ludDY0QXJyYXk6ICdCaWdJbnQ2NEFycmF5JyxcbiAgICBCaWdVaW50NjRBcnJheTogJ0JpZ1VpbnQ2NEFycmF5JyxcbiAgICBCb29sZWFuOiAnQm9vbGVhbicsXG4gICAgRGF0YVZpZXc6ICdEYXRhVmlldycsXG4gICAgRXZhbEVycm9yOiAnRXZhbEVycm9yJyxcbiAgICBGbG9hdDMyQXJyYXk6ICdGbG9hdDMyQXJyYXknLFxuICAgIEZsb2F0NjRBcnJheTogJ0Zsb2F0NjRBcnJheScsXG4gICAgSW50OEFycmF5OiAnSW50OEFycmF5JyxcbiAgICBJbnQxNkFycmF5OiAnSW50MTZBcnJheScsXG4gICAgSW50MzJBcnJheTogJ0ludDMyQXJyYXknLFxuICAgIE1hcDogJ01hcCcsXG4gICAgTnVtYmVyOiAnTnVtYmVyJyxcbiAgICBPYmplY3Q6ICdPYmplY3QnLFxuICAgIFByb21pc2U6ICdQcm9taXNlJyxcbiAgICBQcm94eTogJ1Byb3h5JyxcbiAgICBSYW5nZUVycm9yOiAnUmFuZ2VFcnJvcicsXG4gICAgUmVmZXJlbmNlRXJyb3I6ICdSZWZlcmVuY2VFcnJvcicsXG4gICAgU2V0OiAnU2V0JyxcbiAgICBTdHJpbmc6ICdTdHJpbmcnLFxuICAgIFN5bWJvbDogJ1N5bWJvbCcsXG4gICAgU3ludGF4RXJyb3I6ICdTeW50YXhFcnJvcicsXG4gICAgVHlwZUVycm9yOiAnVHlwZUVycm9yJyxcbiAgICBVaW50OEFycmF5OiAnVWludDhBcnJheScsXG4gICAgVWludDhDbGFtcGVkQXJyYXk6ICdVaW50OENsYW1wZWRBcnJheScsXG4gICAgVWludDE2QXJyYXk6ICdVaW50MTZBcnJheScsXG4gICAgVWludDMyQXJyYXk6ICdVaW50MzJBcnJheScsXG4gICAgVVJJRXJyb3I6ICdVUklFcnJvcicsXG4gICAgV2Vha01hcDogJ1dlYWtNYXAnLFxuICAgIFdlYWtTZXQ6ICdXZWFrU2V0JyxcblxuICAgIC8vICoqKiBPdGhlciBQcm9wZXJ0aWVzIG9mIHRoZSBHbG9iYWwgT2JqZWN0XG5cbiAgICBKU09OOiAnSlNPTicsXG4gICAgUmVmbGVjdDogJ1JlZmxlY3QnLFxuXG4gICAgLy8gKioqIEFubmV4IEJcblxuICAgIGVzY2FwZTogJ2VzY2FwZScsXG4gICAgdW5lc2NhcGU6ICd1bmVzY2FwZScsXG5cbiAgICAvLyBFU05leHRcblxuICAgIGxvY2tkb3duOiAnbG9ja2Rvd24nLFxuICAgIGhhcmRlbjogJ2hhcmRlbicsXG4gICAgSGFuZGxlZFByb21pc2U6ICdIYW5kbGVkUHJvbWlzZScsIC8vIFRPRE86IFVudGlsIFByb21pc2UuZGVsZWdhdGUgKHNlZSBiZWxvdykuXG4gICAgU3RhdGljTW9kdWxlUmVjb3JkOiAnU3RhdGljTW9kdWxlUmVjb3JkJyxcbiAgfTtcblxuICAvKipcbiAgICogaW5pdGlhbEdsb2JhbFByb3BlcnR5TmFtZXNcbiAgICogVGhvc2UgZm91bmQgb25seSBvbiB0aGUgaW5pdGlhbCBnbG9iYWwsIGkuZS4sIHRoZSBnbG9iYWwgb2YgdGhlXG4gICAqIHN0YXJ0IGNvbXBhcnRtZW50LCBhcyB3ZWxsIGFzIGFueSBjb21wYXJ0bWVudHMgY3JlYXRlZCBiZWZvcmUgbG9ja2Rvd24uXG4gICAqIFRoZXNlIG1heSBwcm92aWRlIG11Y2ggb2YgdGhlIHBvd2VyIHByb3ZpZGVkIGJ5IHRoZSBvcmlnaW5hbC5cbiAgICogTWFwcyBmcm9tIHByb3BlcnR5IG5hbWUgdG8gdGhlIGludHJpbnNpYyBuYW1lIGluIHRoZSB3aGl0ZWxpc3QuXG4gICAqL1xuICBjb25zdCBpbml0aWFsR2xvYmFsUHJvcGVydHlOYW1lcyA9IHtcbiAgICAvLyAqKiogQ29uc3RydWN0b3IgUHJvcGVydGllcyBvZiB0aGUgR2xvYmFsIE9iamVjdFxuXG4gICAgRGF0ZTogJyVJbml0aWFsRGF0ZSUnLFxuICAgIEVycm9yOiAnJUluaXRpYWxFcnJvciUnLFxuICAgIFJlZ0V4cDogJyVJbml0aWFsUmVnRXhwJScsXG5cbiAgICAvLyAqKiogT3RoZXIgUHJvcGVydGllcyBvZiB0aGUgR2xvYmFsIE9iamVjdFxuXG4gICAgTWF0aDogJyVJbml0aWFsTWF0aCUnLFxuXG4gICAgLy8gRVNOZXh0XG5cbiAgICAvLyBGcm9tIEVycm9yLXN0YWNrIHByb3Bvc2FsXG4gICAgLy8gT25seSBvbiBpbml0aWFsIGdsb2JhbC4gTm8gY29ycmVzcG9uZGluZ1xuICAgIC8vIHBvd2VybGVzcyBmb3JtIGZvciBvdGhlciBnbG9iYWxzLlxuICAgIGdldFN0YWNrU3RyaW5nOiAnJUluaXRpYWxHZXRTdGFja1N0cmluZyUnLFxuXG4gICAgLy8gVE9ETyBodHRwczovL2dpdGh1Yi5jb20vQWdvcmljL1NFUy1zaGltL2lzc3Vlcy81NTFcbiAgICAvLyBOZWVkIGluaXRpYWwgV2Vha1JlZiBhbmQgRmluYWxpemF0aW9uR3JvdXAgaW5cbiAgICAvLyBzdGFydCBjb21wYXJ0bWVudCBvbmx5LlxuICB9O1xuXG4gIC8qKlxuICAgKiBzaGFyZWRHbG9iYWxQcm9wZXJ0eU5hbWVzXG4gICAqIFRob3NlIGZvdW5kIG9ubHkgb24gdGhlIGdsb2JhbHMgb2YgbmV3IGNvbXBhcnRtZW50cyBjcmVhdGVkIGFmdGVyIGxvY2tkb3duLFxuICAgKiB3aGljaCBtdXN0IHRoZXJlZm9yZSBiZSBwb3dlcmxlc3MuXG4gICAqIE1hcHMgZnJvbSBwcm9wZXJ0eSBuYW1lIHRvIHRoZSBpbnRyaW5zaWMgbmFtZSBpbiB0aGUgd2hpdGVsaXN0LlxuICAgKi9cbiAgY29uc3Qgc2hhcmVkR2xvYmFsUHJvcGVydHlOYW1lcyA9IHtcbiAgICAvLyAqKiogQ29uc3RydWN0b3IgUHJvcGVydGllcyBvZiB0aGUgR2xvYmFsIE9iamVjdFxuXG4gICAgRGF0ZTogJyVTaGFyZWREYXRlJScsXG4gICAgRXJyb3I6ICclU2hhcmVkRXJyb3IlJyxcbiAgICBSZWdFeHA6ICclU2hhcmVkUmVnRXhwJScsXG5cbiAgICAvLyAqKiogT3RoZXIgUHJvcGVydGllcyBvZiB0aGUgR2xvYmFsIE9iamVjdFxuXG4gICAgTWF0aDogJyVTaGFyZWRNYXRoJScsXG4gIH07XG5cbiAgLy8gQWxsIHRoZSBcInN1YmNsYXNzZXNcIiBvZiBFcnJvci4gVGhlc2UgYXJlIGNvbGxlY3RpdmVseSByZXByZXNlbnRlZCBpbiB0aGVcbiAgLy8gRWNtYVNjcmlwdCBzcGVjIGJ5IHRoZSBtZXRhIHZhcmlhYmxlIE5hdGl2ZUVycm9yLlxuICAvLyBUT0RPIEFkZCBBZ2dyZWdhdGVFcnJvciBodHRwczovL2dpdGh1Yi5jb20vQWdvcmljL1NFUy1zaGltL2lzc3Vlcy81NTBcbiAgY29uc3QgTmF0aXZlRXJyb3JzID0gW1xuICAgIEV2YWxFcnJvcixcbiAgICBSYW5nZUVycm9yLFxuICAgIFJlZmVyZW5jZUVycm9yLFxuICAgIFN5bnRheEVycm9yLFxuICAgIFR5cGVFcnJvcixcbiAgICBVUklFcnJvcixcbiAgXTtcblxuICAvKipcbiAgICogPHA+RWFjaCBKU09OIHJlY29yZCBlbnVtZXJhdGVzIHRoZSBkaXNwb3NpdGlvbiBvZiB0aGUgcHJvcGVydGllcyBvblxuICAgKiAgICBzb21lIGNvcnJlc3BvbmRpbmcgaW50cmluc2ljIG9iamVjdC5cbiAgICpcbiAgICogPHA+QWxsIHJlY29yZHMgYXJlIG1hZGUgb2Yga2V5LXZhbHVlIHBhaXJzIHdoZXJlIHRoZSBrZXlcbiAgICogICAgaXMgdGhlIHByb3BlcnR5IHRvIHByb2Nlc3MsIGFuZCB0aGUgdmFsdWUgaXMgdGhlIGFzc29jaWF0ZWRcbiAgICogICAgZGlzcG9zaXRpb25zIGEuay5hLiB0aGUgXCJwZXJtaXRcIi4gVGhvc2UgcGVybWl0cyBjYW4gYmU6XG4gICAqIDx1bD5cbiAgICogPGxpPlRoZSBib29sZWFuIHZhbHVlIFwiZmFsc2VcIiwgaW4gd2hpY2ggY2FzZSB0aGlzIHByb3BlcnR5IGlzXG4gICAqICAgICBibGFja2xpc3RlZCBhbmQgc2ltcGx5IHJlbW92ZWQuIFByb3BlcnRpZXMgbm90IG1lbnRpb25lZFxuICAgKiAgICAgYXJlIGFsc28gY29uc2lkZXJlZCBibGFja2xpc3RlZCBhbmQgYXJlIHJlbW92ZWQuXG4gICAqIDxsaT5BIHN0cmluZyB2YWx1ZSBlcXVhbCB0byBhIHByaW1pdGl2ZSAoXCJudW1iZXJcIiwgXCJzdHJpbmdcIiwgZXRjKSxcbiAgICogICAgIGluIHdoaWNoIGNhc2UgdGhlIHByb3BlcnR5IGlzIHdoaXRlbGlzdGVkIGlmIGl0cyB2YWx1ZSBwcm9wZXJ0eVxuICAgKiAgICAgaXMgdHlwZW9mIHRoZSBnaXZlbiB0eXBlLiBGb3IgZXhhbXBsZSwge0Bjb2RlIFwiSW5maW5pdHlcIn0gbGVhZHMgdG9cbiAgICogICAgIFwibnVtYmVyXCIgYW5kIHByb3BlcnR5IHZhbHVlcyB0aGF0IGZhaWwge0Bjb2RlIHR5cGVvZiBcIm51bWJlclwifS5cbiAgICogICAgIGFyZSByZW1vdmVkLlxuICAgKiA8bGk+QSBzdHJpbmcgdmFsdWUgZXF1YWwgdG8gYW4gaW50aW5zaWMgbmFtZSAoXCJPYmplY3RQcm90b3R5cGVcIixcbiAgICogICAgIFwiQXJyYXlcIiwgZXRjKSwgaW4gd2hpY2ggY2FzZSB0aGUgcHJvcGVydHkgd2hpdGVsaXN0ZWQgaWYgaXRzXG4gICAqICAgICB2YWx1ZSBwcm9wZXJ0eSBpcyBlcXVhbCB0byB0aGUgdmFsdWUgb2YgdGhlIGNvcnJlc3BvbmZpbmdcbiAgICogICAgIGludHJpbnNpY3MuIEZvciBleGFtcGxlLCB7QGNvZGUgTWFwLnByb3RvdHlwZX0gbGVhZHMgdG9cbiAgICogICAgIFwiTWFwUHJvdG90eXBlXCIgYW5kIHRoZSBwcm9wZXJ0eSBpcyByZW1vdmVkIGlmIGl0cyB2YWx1ZSBpc1xuICAgKiAgICAgbm90IGVxdWFsIHRvICVNYXBQcm90b3R5cGUlXG4gICAqIDxsaT5Bbm90aGVyIHJlY29yZCwgaW4gd2hpY2ggY2FzZSB0aGlzIHByb3BlcnR5IGlzIHNpbXBseVxuICAgKiAgICAgd2hpdGVsaXN0ZWQgYW5kIHRoYXQgbmV4dCByZWNvcmQgcmVwcmVzZW50cyB0aGUgZGlzcG9zaXRpb24gb2ZcbiAgICogICAgIHRoZSBvYmplY3Qgd2hpY2ggaXMgaXRzIHZhbHVlLiBGb3IgZXhhbXBsZSwge0Bjb2RlIFwiT2JqZWN0XCJ9XG4gICAqICAgICBsZWFkcyB0byBhbm90aGVyIHJlY29yZCBleHBsYWluaW5nIHdoYXQgcHJvcGVydGllcyB7QGNvZGVcbiAgICogICAgIFwiT2JqZWN0XCJ9IG1heSBoYXZlIGFuZCBob3cgZWFjaCBzdWNoIHByb3BlcnR5IHNob3VsZCBiZSB0cmVhdGVkLlxuICAgKlxuICAgKiA8cD5Ob3RlczpcbiAgICogPGxpPlwiW1tQcm90b11dXCIgaXMgdXNlZCB0byByZWZlciB0byB0aGUgXCJbW1Byb3RvdHlwZV1dXCIgaW50ZXJuYWxcbiAgICogICAgIHNsb3QsIHdoaWNoIHNheXMgd2hpY2ggb2JqZWN0IHRoaXMgb2JqZWN0IGluaGVyaXRzIGZyb20uXG4gICAqIDxsaT5cIi0tcHJvdG8tLVwiIGlzIHVzZWQgdG8gcmVmZXIgdG8gdGhlIFwiX19wcm90b19fXCIgcHJvcGVydHkgbmFtZSxcbiAgICogICAgIHdoaWNoIGlzIHRoZSBuYW1lIG9mIGFuIGFjY2Vzc29yIHByb3BlcnR5IG9uIE9iamVjdC5wcm90b3R5cGUuXG4gICAqICAgICBJbiBwcmFjdGljZSwgaXQgaXMgdXNlZCB0byBhY2Nlc3MgdGhlIFtbUHJvdG9dXSBpbnRlcm5hbCBzbG90LFxuICAgKiAgICAgYnV0IGlzIGRpc3RpbmN0IGZyb20gdGhlIGludGVybmFsIHNsb3QgaXRzZWxmLiBXZSB1c2VcbiAgICogICAgIFwiLS1wcm90by0tXCIgcmF0aGVyIHRoYW4gXCJfX3Byb3RvX19cIiBiZWxvdyBiZWNhdXNlIFwiX19wcm90b19fXCJcbiAgICogICAgIGluIGFuIG9iamVjdCBsaXRlcmFsIGlzIHNwZWNpYWwgc3ludGF4IHJhdGhlciB0aGFuIGEgbm9ybWFsXG4gICAqICAgICBwcm9wZXJ0eSBkZWZpbml0aW9uLlxuICAgKiA8bGk+XCJPYmplY3RQcm90b3R5cGVcIiBpcyB0aGUgZGVmYXVsdCBcIltbUHJvdG9dXVwiICh3aGVuIG5vdCBzcGVjaWZpZWQpLlxuICAgKiA8bGk+Q29uc3RhbnRzIFwiZm5cIiBhbmQgXCJnZXR0ZXJcIiBhcmUgdXNlZCB0byBrZWVwIHRoZSBzdHJ1Y3R1cmUgRFJZLlxuICAgKiA8bGk+U3ltYm9sIHByb3BlcnRpZXMgYXJlIGxpc3RlZCB1c2luZyB0aGUgXCJAQG5hbWVcIiBmb3JtLlxuICAgKi9cblxuICAvLyBGdW5jdGlvbiBJbnN0YW5jZXNcbiAgY29uc3QgRnVuY3Rpb25JbnN0YW5jZSA9IHtcbiAgICAnW1tQcm90b11dJzogJyVGdW5jdGlvblByb3RvdHlwZSUnLFxuICAgIGxlbmd0aDogJ251bWJlcicsXG4gICAgbmFtZTogJ3N0cmluZycsXG4gICAgLy8gRG8gbm90IHNwZWNpZnkgXCJwcm90b3R5cGVcIiBoZXJlLCBzaW5jZSBvbmx5IEZ1bmN0aW9uIGluc3RhbmNlcyB0aGF0IGNhblxuICAgIC8vIGJlIHVzZWQgYXMgYSBjb25zdHJ1Y3RvciBoYXZlIGEgcHJvdG90eXBlIHByb3BlcnR5LiBGb3IgY29uc3RydWN0b3JzLFxuICAgIC8vIHNpbmNlIHByb3RvdHlwZSBwcm9wZXJ0aWVzIGFyZSBpbnN0YW5jZS1zcGVjaWZpYywgd2UgZGVmaW5lIGl0IHRoZXJlLlxuICB9O1xuXG4gIC8vIEFsaWFzZXNcbiAgY29uc3QgZm4gPSBGdW5jdGlvbkluc3RhbmNlO1xuXG4gIGNvbnN0IGdldHRlciA9IHtcbiAgICBnZXQ6IGZuLFxuICAgIHNldDogJ3VuZGVmaW5lZCcsXG4gIH07XG5cbiAgLy8gUG9zc2libGUgYnV0IG5vdCBlbmNvdW50ZXJlZCBpbiB0aGUgc3BlY3NcbiAgLy8gZXhwb3J0IGNvbnN0IHNldHRlciA9IHtcbiAgLy8gICBnZXQ6ICd1bmRlZmluZWQnLFxuICAvLyAgIHNldDogZm4sXG4gIC8vIH07XG5cbiAgY29uc3QgYWNjZXNzb3IgPSB7XG4gICAgZ2V0OiBmbixcbiAgICBzZXQ6IGZuLFxuICB9O1xuXG4gIGZ1bmN0aW9uIGlzQWNjZXNzb3JQZXJtaXQocGVybWl0KSB7XG4gICAgcmV0dXJuIHBlcm1pdCA9PT0gZ2V0dGVyIHx8IHBlcm1pdCA9PT0gYWNjZXNzb3I7XG4gIH1cblxuICAvLyBOYXRpdmVFcnJvciBPYmplY3QgU3RydWN0dXJlXG4gIGZ1bmN0aW9uIE5hdGl2ZUVycm9yKHByb3RvdHlwZSkge1xuICAgIHJldHVybiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBOYXRpdmVFcnJvciBDb25zdHJ1Y3RvcnNcbiAgICAgICdbW1Byb3RvXV0nOiAnJVNoYXJlZEVycm9yJScsXG5cbiAgICAgIC8vIE5hdGl2ZUVycm9yLnByb3RvdHlwZVxuICAgICAgcHJvdG90eXBlLFxuICAgIH07XG4gIH1cblxuICBmdW5jdGlvbiBOYXRpdmVFcnJvclByb3RvdHlwZShjb25zdHJ1Y3Rvcikge1xuICAgIHJldHVybiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBOYXRpdmVFcnJvciBQcm90b3R5cGUgT2JqZWN0c1xuICAgICAgJ1tbUHJvdG9dXSc6ICclRXJyb3JQcm90b3R5cGUlJyxcbiAgICAgIGNvbnN0cnVjdG9yLFxuICAgICAgbWVzc2FnZTogJ3N0cmluZycsXG4gICAgICBuYW1lOiAnc3RyaW5nJyxcbiAgICAgIC8vIFJlZHVuZGFudGx5IHByZXNlbnQgb25seSBvbiB2OC4gU2FmZSB0byByZW1vdmUuXG4gICAgICB0b1N0cmluZzogZmFsc2UsXG4gICAgfTtcbiAgfVxuXG4gIC8vIFRoZSBUeXBlZEFycmF5IENvbnN0cnVjdG9yc1xuICBmdW5jdGlvbiBUeXBlZEFycmF5KHByb3RvdHlwZSkge1xuICAgIHJldHVybiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBUeXBlZEFycmF5IENvbnN0cnVjdG9yc1xuICAgICAgJ1tbUHJvdG9dXSc6ICclVHlwZWRBcnJheSUnLFxuICAgICAgQllURVNfUEVSX0VMRU1FTlQ6ICdudW1iZXInLFxuICAgICAgcHJvdG90eXBlLFxuICAgIH07XG4gIH1cblxuICBmdW5jdGlvbiBUeXBlZEFycmF5UHJvdG90eXBlKGNvbnN0cnVjdG9yKSB7XG4gICAgcmV0dXJuIHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIFR5cGVkQXJyYXkgUHJvdG90eXBlIE9iamVjdHNcbiAgICAgICdbW1Byb3RvXV0nOiAnJVR5cGVkQXJyYXlQcm90b3R5cGUlJyxcbiAgICAgIEJZVEVTX1BFUl9FTEVNRU5UOiAnbnVtYmVyJyxcbiAgICAgIGNvbnN0cnVjdG9yLFxuICAgIH07XG4gIH1cblxuICAvLyBXaXRob3V0IE1hdGgucmFuZG9tXG4gIGNvbnN0IFNoYXJlZE1hdGggPSB7XG4gICAgRTogJ251bWJlcicsXG4gICAgTE4xMDogJ251bWJlcicsXG4gICAgTE4yOiAnbnVtYmVyJyxcbiAgICBMT0cxMEU6ICdudW1iZXInLFxuICAgIExPRzJFOiAnbnVtYmVyJyxcbiAgICBQSTogJ251bWJlcicsXG4gICAgU1FSVDFfMjogJ251bWJlcicsXG4gICAgU1FSVDI6ICdudW1iZXInLFxuICAgICdAQHRvU3RyaW5nVGFnJzogJ3N0cmluZycsXG4gICAgYWJzOiBmbixcbiAgICBhY29zOiBmbixcbiAgICBhY29zaDogZm4sXG4gICAgYXNpbjogZm4sXG4gICAgYXNpbmg6IGZuLFxuICAgIGF0YW46IGZuLFxuICAgIGF0YW5oOiBmbixcbiAgICBhdGFuMjogZm4sXG4gICAgY2JydDogZm4sXG4gICAgY2VpbDogZm4sXG4gICAgY2x6MzI6IGZuLFxuICAgIGNvczogZm4sXG4gICAgY29zaDogZm4sXG4gICAgZXhwOiBmbixcbiAgICBleHBtMTogZm4sXG4gICAgZmxvb3I6IGZuLFxuICAgIGZyb3VuZDogZm4sXG4gICAgaHlwb3Q6IGZuLFxuICAgIGltdWw6IGZuLFxuICAgIGxvZzogZm4sXG4gICAgbG9nMXA6IGZuLFxuICAgIGxvZzEwOiBmbixcbiAgICBsb2cyOiBmbixcbiAgICBtYXg6IGZuLFxuICAgIG1pbjogZm4sXG4gICAgcG93OiBmbixcbiAgICByb3VuZDogZm4sXG4gICAgc2lnbjogZm4sXG4gICAgc2luOiBmbixcbiAgICBzaW5oOiBmbixcbiAgICBzcXJ0OiBmbixcbiAgICB0YW46IGZuLFxuICAgIHRhbmg6IGZuLFxuICAgIHRydW5jOiBmbixcbiAgICAvLyBTZWUgaHR0cHM6Ly9naXRodWIuY29tL01vZGRhYmxlLU9wZW5Tb3VyY2UvbW9kZGFibGUvaXNzdWVzLzUyM1xuICAgIGlkaXY6IGZhbHNlLFxuICAgIC8vIFNlZSBodHRwczovL2dpdGh1Yi5jb20vTW9kZGFibGUtT3BlblNvdXJjZS9tb2RkYWJsZS9pc3N1ZXMvNTIzXG4gICAgaWRpdm1vZDogZmFsc2UsXG4gICAgLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9Nb2RkYWJsZS1PcGVuU291cmNlL21vZGRhYmxlL2lzc3Vlcy81MjNcbiAgICBpbW9kOiBmYWxzZSxcbiAgICAvLyBTZWUgaHR0cHM6Ly9naXRodWIuY29tL01vZGRhYmxlLU9wZW5Tb3VyY2UvbW9kZGFibGUvaXNzdWVzLzUyM1xuICAgIGltdWxkaXY6IGZhbHNlLFxuICAgIC8vIFNlZSBodHRwczovL2dpdGh1Yi5jb20vTW9kZGFibGUtT3BlblNvdXJjZS9tb2RkYWJsZS9pc3N1ZXMvNTIzXG4gICAgaXJlbTogZmFsc2UsXG4gICAgLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9Nb2RkYWJsZS1PcGVuU291cmNlL21vZGRhYmxlL2lzc3Vlcy81MjNcbiAgICBtb2Q6IGZhbHNlLFxuICB9O1xuXG4gIGNvbnN0IHdoaXRlbGlzdCA9IHtcbiAgICAvLyBFQ01BIGh0dHBzOi8vdGMzOS5lcy9lY21hMjYyXG5cbiAgICAvLyBUaGUgaW50cmluc2ljcyBvYmplY3QgaGFzIG5vIHByb3RvdHlwZSB0byBhdm9pZCBjb25mbGljdHMuXG4gICAgJ1tbUHJvdG9dXSc6IG51bGwsXG5cbiAgICAvLyAlVGhyb3dUeXBlRXJyb3IlXG4gICAgJyVUaHJvd1R5cGVFcnJvciUnOiBmbixcblxuICAgIC8vICoqKiBUaGUgR2xvYmFsIE9iamVjdFxuXG4gICAgLy8gKioqIFZhbHVlIFByb3BlcnRpZXMgb2YgdGhlIEdsb2JhbCBPYmplY3RcbiAgICBJbmZpbml0eTogJ251bWJlcicsXG4gICAgTmFOOiAnbnVtYmVyJyxcbiAgICB1bmRlZmluZWQ6ICd1bmRlZmluZWQnLFxuXG4gICAgLy8gKioqIEZ1bmN0aW9uIFByb3BlcnRpZXMgb2YgdGhlIEdsb2JhbCBPYmplY3RcblxuICAgIC8vIGV2YWxcbiAgICAnJVVuaXF1ZUV2YWwlJzogZm4sXG4gICAgaXNGaW5pdGU6IGZuLFxuICAgIGlzTmFOOiBmbixcbiAgICBwYXJzZUZsb2F0OiBmbixcbiAgICBwYXJzZUludDogZm4sXG4gICAgZGVjb2RlVVJJOiBmbixcbiAgICBkZWNvZGVVUklDb21wb25lbnQ6IGZuLFxuICAgIGVuY29kZVVSSTogZm4sXG4gICAgZW5jb2RlVVJJQ29tcG9uZW50OiBmbixcblxuICAgIC8vICoqKiBGdW5kYW1lbnRhbCBPYmplY3RzXG5cbiAgICBPYmplY3Q6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIE9iamVjdCBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIGFzc2lnbjogZm4sXG4gICAgICBjcmVhdGU6IGZuLFxuICAgICAgZGVmaW5lUHJvcGVydGllczogZm4sXG4gICAgICBkZWZpbmVQcm9wZXJ0eTogZm4sXG4gICAgICBlbnRyaWVzOiBmbixcbiAgICAgIGZyZWV6ZTogZm4sXG4gICAgICBmcm9tRW50cmllczogZm4sXG4gICAgICBnZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3I6IGZuLFxuICAgICAgZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yczogZm4sXG4gICAgICBnZXRPd25Qcm9wZXJ0eU5hbWVzOiBmbixcbiAgICAgIGdldE93blByb3BlcnR5U3ltYm9sczogZm4sXG4gICAgICBnZXRQcm90b3R5cGVPZjogZm4sXG4gICAgICBpczogZm4sXG4gICAgICBpc0V4dGVuc2libGU6IGZuLFxuICAgICAgaXNGcm96ZW46IGZuLFxuICAgICAgaXNTZWFsZWQ6IGZuLFxuICAgICAga2V5czogZm4sXG4gICAgICBwcmV2ZW50RXh0ZW5zaW9uczogZm4sXG4gICAgICBwcm90b3R5cGU6ICclT2JqZWN0UHJvdG90eXBlJScsXG4gICAgICBzZWFsOiBmbixcbiAgICAgIHNldFByb3RvdHlwZU9mOiBmbixcbiAgICAgIHZhbHVlczogZm4sXG4gICAgfSxcblxuICAgICclT2JqZWN0UHJvdG90eXBlJSc6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIE9iamVjdCBQcm90b3R5cGUgT2JqZWN0XG4gICAgICAnW1tQcm90b11dJzogbnVsbCxcbiAgICAgIGNvbnN0cnVjdG9yOiAnT2JqZWN0JyxcbiAgICAgIGhhc093blByb3BlcnR5OiBmbixcbiAgICAgIGlzUHJvdG90eXBlT2Y6IGZuLFxuICAgICAgcHJvcGVydHlJc0VudW1lcmFibGU6IGZuLFxuICAgICAgdG9Mb2NhbGVTdHJpbmc6IGZuLFxuICAgICAgdG9TdHJpbmc6IGZuLFxuICAgICAgdmFsdWVPZjogZm4sXG5cbiAgICAgIC8vIEFubmV4IEI6IEFkZGl0aW9uYWwgUHJvcGVydGllcyBvZiB0aGUgT2JqZWN0LnByb3RvdHlwZSBPYmplY3RcblxuICAgICAgJy0tcHJvdG8tLSc6IGFjY2Vzc29yLFxuICAgICAgX19kZWZpbmVHZXR0ZXJfXzogZm4sXG4gICAgICBfX2RlZmluZVNldHRlcl9fOiBmbixcbiAgICAgIF9fbG9va3VwR2V0dGVyX186IGZuLFxuICAgICAgX19sb29rdXBTZXR0ZXJfXzogZm4sXG4gICAgfSxcblxuICAgICclVW5pcXVlRnVuY3Rpb24lJzoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgRnVuY3Rpb24gQ29uc3RydWN0b3JcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBwcm90b3R5cGU6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICB9LFxuXG4gICAgJyVJbmVydEZ1bmN0aW9uJSc6IHtcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBwcm90b3R5cGU6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICB9LFxuXG4gICAgJyVGdW5jdGlvblByb3RvdHlwZSUnOiB7XG4gICAgICBhcHBseTogZm4sXG4gICAgICBiaW5kOiBmbixcbiAgICAgIGNhbGw6IGZuLFxuICAgICAgY29uc3RydWN0b3I6ICclSW5lcnRGdW5jdGlvbiUnLCAvLyBUT0RPIHRlc3RcbiAgICAgIHRvU3RyaW5nOiBmbixcbiAgICAgICdAQGhhc0luc3RhbmNlJzogZm4sXG4gICAgICAvLyBwcm9wb3NlZCBidXQgbm90IHlldCBzdGQgeWV0LiBUbyBiZSByZW1vdmVkIGlmIHRoZXJlXG4gICAgICBjYWxsZXI6IGZhbHNlLFxuICAgICAgLy8gcHJvcG9zZWQgYnV0IG5vdCB5ZXQgc3RkIHlldC4gVG8gYmUgcmVtb3ZlZCBpZiB0aGVyZVxuICAgICAgYXJndW1lbnRzOiBmYWxzZSxcbiAgICB9LFxuXG4gICAgQm9vbGVhbjoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgQm9vbGVhbiBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIHByb3RvdHlwZTogJyVCb29sZWFuUHJvdG90eXBlJScsXG4gICAgfSxcblxuICAgICclQm9vbGVhblByb3RvdHlwZSUnOiB7XG4gICAgICBjb25zdHJ1Y3RvcjogJ0Jvb2xlYW4nLFxuICAgICAgdG9TdHJpbmc6IGZuLFxuICAgICAgdmFsdWVPZjogZm4sXG4gICAgfSxcblxuICAgIFN5bWJvbDoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgU3ltYm9sIENvbnN0cnVjdG9yXG4gICAgICAnW1tQcm90b11dJzogJyVGdW5jdGlvblByb3RvdHlwZSUnLFxuICAgICAgYXN5bmNJdGVyYXRvcjogJ3N5bWJvbCcsXG4gICAgICBmb3I6IGZuLFxuICAgICAgaGFzSW5zdGFuY2U6ICdzeW1ib2wnLFxuICAgICAgaXNDb25jYXRTcHJlYWRhYmxlOiAnc3ltYm9sJyxcbiAgICAgIGl0ZXJhdG9yOiAnc3ltYm9sJyxcbiAgICAgIGtleUZvcjogZm4sXG4gICAgICBtYXRjaDogJ3N5bWJvbCcsXG4gICAgICBtYXRjaEFsbDogJ3N5bWJvbCcsXG4gICAgICBwcm90b3R5cGU6ICclU3ltYm9sUHJvdG90eXBlJScsXG4gICAgICByZXBsYWNlOiAnc3ltYm9sJyxcbiAgICAgIHNlYXJjaDogJ3N5bWJvbCcsXG4gICAgICBzcGVjaWVzOiAnc3ltYm9sJyxcbiAgICAgIHNwbGl0OiAnc3ltYm9sJyxcbiAgICAgIHRvUHJpbWl0aXZlOiAnc3ltYm9sJyxcbiAgICAgIHRvU3RyaW5nVGFnOiAnc3ltYm9sJyxcbiAgICAgIHVuc2NvcGFibGVzOiAnc3ltYm9sJyxcbiAgICB9LFxuXG4gICAgJyVTeW1ib2xQcm90b3R5cGUlJzoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgU3ltYm9sIFByb3RvdHlwZSBPYmplY3RcbiAgICAgIGNvbnN0cnVjdG9yOiAnU3ltYm9sJyxcbiAgICAgIGRlc2NyaXB0aW9uOiBnZXR0ZXIsXG4gICAgICB0b1N0cmluZzogZm4sXG4gICAgICB2YWx1ZU9mOiBmbixcbiAgICAgICdAQHRvUHJpbWl0aXZlJzogZm4sXG4gICAgICAnQEB0b1N0cmluZ1RhZyc6ICdzdHJpbmcnLFxuICAgIH0sXG5cbiAgICAnJUluaXRpYWxFcnJvciUnOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBFcnJvciBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIHByb3RvdHlwZTogJyVFcnJvclByb3RvdHlwZSUnLFxuICAgICAgLy8gTm9uIHN0YW5kYXJkLCB2OCBvbmx5LCB1c2VkIGJ5IHRhcFxuICAgICAgY2FwdHVyZVN0YWNrVHJhY2U6IGZuLFxuICAgICAgLy8gTm9uIHN0YW5kYXJkLCB2OCBvbmx5LCB1c2VkIGJ5IHRhcCwgdGFtZWQgdG8gYWNjZXNzb3JcbiAgICAgIHN0YWNrVHJhY2VMaW1pdDogYWNjZXNzb3IsXG4gICAgICAvLyBOb24gc3RhbmRhcmQsIHY4IG9ubHksIHVzZWQgYnkgc2V2ZXJhbCwgdGFtZWQgdG8gYWNjZXNzb3JcbiAgICAgIHByZXBhcmVTdGFja1RyYWNlOiBhY2Nlc3NvcixcbiAgICB9LFxuXG4gICAgJyVTaGFyZWRFcnJvciUnOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBFcnJvciBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIHByb3RvdHlwZTogJyVFcnJvclByb3RvdHlwZSUnLFxuICAgICAgLy8gTm9uIHN0YW5kYXJkLCB2OCBvbmx5LCB1c2VkIGJ5IHRhcFxuICAgICAgY2FwdHVyZVN0YWNrVHJhY2U6IGZuLFxuICAgICAgLy8gTm9uIHN0YW5kYXJkLCB2OCBvbmx5LCB1c2VkIGJ5IHRhcCwgdGFtZWQgdG8gYWNjZXNzb3JcbiAgICAgIHN0YWNrVHJhY2VMaW1pdDogYWNjZXNzb3IsXG4gICAgICAvLyBOb24gc3RhbmRhcmQsIHY4IG9ubHksIHVzZWQgYnkgc2V2ZXJhbCwgdGFtZWQgdG8gYWNjZXNzb3JcbiAgICAgIHByZXBhcmVTdGFja1RyYWNlOiBhY2Nlc3NvcixcbiAgICB9LFxuXG4gICAgJyVFcnJvclByb3RvdHlwZSUnOiB7XG4gICAgICBjb25zdHJ1Y3RvcjogJyVTaGFyZWRFcnJvciUnLFxuICAgICAgbWVzc2FnZTogJ3N0cmluZycsXG4gICAgICBuYW1lOiAnc3RyaW5nJyxcbiAgICAgIHRvU3RyaW5nOiBmbixcbiAgICAgIC8vIHByb3Bvc2VkIGRlLWZhY3RvLCBhc3N1bWVkIFRPRE9cbiAgICAgIC8vIFNlZW4gb24gRkYgTmlnaHRseSA4OC4wYTFcbiAgICAgIGF0OiBmYWxzZSxcbiAgICAgIC8vIFNlZW4gb24gRkYgYW5kIFhTXG4gICAgICBzdGFjazogZmFsc2UsXG4gICAgfSxcblxuICAgIC8vIE5hdGl2ZUVycm9yXG5cbiAgICBFdmFsRXJyb3I6IE5hdGl2ZUVycm9yKCclRXZhbEVycm9yUHJvdG90eXBlJScpLFxuICAgIFJhbmdlRXJyb3I6IE5hdGl2ZUVycm9yKCclUmFuZ2VFcnJvclByb3RvdHlwZSUnKSxcbiAgICBSZWZlcmVuY2VFcnJvcjogTmF0aXZlRXJyb3IoJyVSZWZlcmVuY2VFcnJvclByb3RvdHlwZSUnKSxcbiAgICBTeW50YXhFcnJvcjogTmF0aXZlRXJyb3IoJyVTeW50YXhFcnJvclByb3RvdHlwZSUnKSxcbiAgICBUeXBlRXJyb3I6IE5hdGl2ZUVycm9yKCclVHlwZUVycm9yUHJvdG90eXBlJScpLFxuICAgIFVSSUVycm9yOiBOYXRpdmVFcnJvcignJVVSSUVycm9yUHJvdG90eXBlJScpLFxuXG4gICAgJyVFdmFsRXJyb3JQcm90b3R5cGUlJzogTmF0aXZlRXJyb3JQcm90b3R5cGUoJ0V2YWxFcnJvcicpLFxuICAgICclUmFuZ2VFcnJvclByb3RvdHlwZSUnOiBOYXRpdmVFcnJvclByb3RvdHlwZSgnUmFuZ2VFcnJvcicpLFxuICAgICclUmVmZXJlbmNlRXJyb3JQcm90b3R5cGUlJzogTmF0aXZlRXJyb3JQcm90b3R5cGUoJ1JlZmVyZW5jZUVycm9yJyksXG4gICAgJyVTeW50YXhFcnJvclByb3RvdHlwZSUnOiBOYXRpdmVFcnJvclByb3RvdHlwZSgnU3ludGF4RXJyb3InKSxcbiAgICAnJVR5cGVFcnJvclByb3RvdHlwZSUnOiBOYXRpdmVFcnJvclByb3RvdHlwZSgnVHlwZUVycm9yJyksXG4gICAgJyVVUklFcnJvclByb3RvdHlwZSUnOiBOYXRpdmVFcnJvclByb3RvdHlwZSgnVVJJRXJyb3InKSxcblxuICAgIC8vICoqKiBOdW1iZXJzIGFuZCBEYXRlc1xuXG4gICAgTnVtYmVyOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBOdW1iZXIgQ29uc3RydWN0b3JcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBFUFNJTE9OOiAnbnVtYmVyJyxcbiAgICAgIGlzRmluaXRlOiBmbixcbiAgICAgIGlzSW50ZWdlcjogZm4sXG4gICAgICBpc05hTjogZm4sXG4gICAgICBpc1NhZmVJbnRlZ2VyOiBmbixcbiAgICAgIE1BWF9TQUZFX0lOVEVHRVI6ICdudW1iZXInLFxuICAgICAgTUFYX1ZBTFVFOiAnbnVtYmVyJyxcbiAgICAgIE1JTl9TQUZFX0lOVEVHRVI6ICdudW1iZXInLFxuICAgICAgTUlOX1ZBTFVFOiAnbnVtYmVyJyxcbiAgICAgIE5hTjogJ251bWJlcicsXG4gICAgICBORUdBVElWRV9JTkZJTklUWTogJ251bWJlcicsXG4gICAgICBwYXJzZUZsb2F0OiBmbixcbiAgICAgIHBhcnNlSW50OiBmbixcbiAgICAgIFBPU0lUSVZFX0lORklOSVRZOiAnbnVtYmVyJyxcbiAgICAgIHByb3RvdHlwZTogJyVOdW1iZXJQcm90b3R5cGUlJyxcbiAgICB9LFxuXG4gICAgJyVOdW1iZXJQcm90b3R5cGUlJzoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgTnVtYmVyIFByb3RvdHlwZSBPYmplY3RcbiAgICAgIGNvbnN0cnVjdG9yOiAnTnVtYmVyJyxcbiAgICAgIHRvRXhwb25lbnRpYWw6IGZuLFxuICAgICAgdG9GaXhlZDogZm4sXG4gICAgICB0b0xvY2FsZVN0cmluZzogZm4sXG4gICAgICB0b1ByZWNpc2lvbjogZm4sXG4gICAgICB0b1N0cmluZzogZm4sXG4gICAgICB2YWx1ZU9mOiBmbixcbiAgICB9LFxuXG4gICAgQmlnSW50OiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBCaWdJbnQgQ29uc3RydWN0b3JcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBhc0ludE46IGZuLFxuICAgICAgYXNVaW50TjogZm4sXG4gICAgICBwcm90b3R5cGU6ICclQmlnSW50UHJvdG90eXBlJScsXG4gICAgICAvLyBTZWUgaHR0cHM6Ly9naXRodWIuY29tL01vZGRhYmxlLU9wZW5Tb3VyY2UvbW9kZGFibGUvaXNzdWVzLzUyM1xuICAgICAgYml0TGVuZ3RoOiBmYWxzZSxcbiAgICAgIC8vIFNlZSBodHRwczovL2dpdGh1Yi5jb20vTW9kZGFibGUtT3BlblNvdXJjZS9tb2RkYWJsZS9pc3N1ZXMvNTIzXG4gICAgICBmcm9tQXJyYXlCdWZmZXI6IGZhbHNlLFxuICAgIH0sXG5cbiAgICAnJUJpZ0ludFByb3RvdHlwZSUnOiB7XG4gICAgICBjb25zdHJ1Y3RvcjogJ0JpZ0ludCcsXG4gICAgICB0b0xvY2FsZVN0cmluZzogZm4sXG4gICAgICB0b1N0cmluZzogZm4sXG4gICAgICB2YWx1ZU9mOiBmbixcbiAgICAgICdAQHRvU3RyaW5nVGFnJzogJ3N0cmluZycsXG4gICAgfSxcblxuICAgICclSW5pdGlhbE1hdGglJzoge1xuICAgICAgLi4uU2hhcmVkTWF0aCxcbiAgICAgIC8vIHJhbmRvbSBpcyBzdGFuZGFyZCBidXQgb21pdHRlZCBmcm9tIFNoYXJlZE1hdGhcbiAgICAgIHJhbmRvbTogZm4sXG4gICAgfSxcblxuICAgICclU2hhcmVkTWF0aCUnOiBTaGFyZWRNYXRoLFxuXG4gICAgJyVJbml0aWFsRGF0ZSUnOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBEYXRlIENvbnN0cnVjdG9yXG4gICAgICAnW1tQcm90b11dJzogJyVGdW5jdGlvblByb3RvdHlwZSUnLFxuICAgICAgbm93OiBmbixcbiAgICAgIHBhcnNlOiBmbixcbiAgICAgIHByb3RvdHlwZTogJyVEYXRlUHJvdG90eXBlJScsXG4gICAgICBVVEM6IGZuLFxuICAgIH0sXG5cbiAgICAnJVNoYXJlZERhdGUlJzoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgRGF0ZSBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIG5vdzogZm4sXG4gICAgICBwYXJzZTogZm4sXG4gICAgICBwcm90b3R5cGU6ICclRGF0ZVByb3RvdHlwZSUnLFxuICAgICAgVVRDOiBmbixcbiAgICB9LFxuXG4gICAgJyVEYXRlUHJvdG90eXBlJSc6IHtcbiAgICAgIGNvbnN0cnVjdG9yOiAnJVNoYXJlZERhdGUlJyxcbiAgICAgIGdldERhdGU6IGZuLFxuICAgICAgZ2V0RGF5OiBmbixcbiAgICAgIGdldEZ1bGxZZWFyOiBmbixcbiAgICAgIGdldEhvdXJzOiBmbixcbiAgICAgIGdldE1pbGxpc2Vjb25kczogZm4sXG4gICAgICBnZXRNaW51dGVzOiBmbixcbiAgICAgIGdldE1vbnRoOiBmbixcbiAgICAgIGdldFNlY29uZHM6IGZuLFxuICAgICAgZ2V0VGltZTogZm4sXG4gICAgICBnZXRUaW1lem9uZU9mZnNldDogZm4sXG4gICAgICBnZXRVVENEYXRlOiBmbixcbiAgICAgIGdldFVUQ0RheTogZm4sXG4gICAgICBnZXRVVENGdWxsWWVhcjogZm4sXG4gICAgICBnZXRVVENIb3VyczogZm4sXG4gICAgICBnZXRVVENNaWxsaXNlY29uZHM6IGZuLFxuICAgICAgZ2V0VVRDTWludXRlczogZm4sXG4gICAgICBnZXRVVENNb250aDogZm4sXG4gICAgICBnZXRVVENTZWNvbmRzOiBmbixcbiAgICAgIHNldERhdGU6IGZuLFxuICAgICAgc2V0RnVsbFllYXI6IGZuLFxuICAgICAgc2V0SG91cnM6IGZuLFxuICAgICAgc2V0TWlsbGlzZWNvbmRzOiBmbixcbiAgICAgIHNldE1pbnV0ZXM6IGZuLFxuICAgICAgc2V0TW9udGg6IGZuLFxuICAgICAgc2V0U2Vjb25kczogZm4sXG4gICAgICBzZXRUaW1lOiBmbixcbiAgICAgIHNldFVUQ0RhdGU6IGZuLFxuICAgICAgc2V0VVRDRnVsbFllYXI6IGZuLFxuICAgICAgc2V0VVRDSG91cnM6IGZuLFxuICAgICAgc2V0VVRDTWlsbGlzZWNvbmRzOiBmbixcbiAgICAgIHNldFVUQ01pbnV0ZXM6IGZuLFxuICAgICAgc2V0VVRDTW9udGg6IGZuLFxuICAgICAgc2V0VVRDU2Vjb25kczogZm4sXG4gICAgICB0b0RhdGVTdHJpbmc6IGZuLFxuICAgICAgdG9JU09TdHJpbmc6IGZuLFxuICAgICAgdG9KU09OOiBmbixcbiAgICAgIHRvTG9jYWxlRGF0ZVN0cmluZzogZm4sXG4gICAgICB0b0xvY2FsZVN0cmluZzogZm4sXG4gICAgICB0b0xvY2FsZVRpbWVTdHJpbmc6IGZuLFxuICAgICAgdG9TdHJpbmc6IGZuLFxuICAgICAgdG9UaW1lU3RyaW5nOiBmbixcbiAgICAgIHRvVVRDU3RyaW5nOiBmbixcbiAgICAgIHZhbHVlT2Y6IGZuLFxuICAgICAgJ0BAdG9QcmltaXRpdmUnOiBmbixcblxuICAgICAgLy8gQW5uZXggQjogQWRkaXRpb25hbCBQcm9wZXJ0aWVzIG9mIHRoZSBEYXRlLnByb3RvdHlwZSBPYmplY3RcbiAgICAgIGdldFllYXI6IGZuLFxuICAgICAgc2V0WWVhcjogZm4sXG4gICAgICB0b0dNVFN0cmluZzogZm4sXG4gICAgfSxcblxuICAgIC8vIFRleHQgUHJvY2Vzc2luZ1xuXG4gICAgU3RyaW5nOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBTdHJpbmcgQ29uc3RydWN0b3JcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBmcm9tQ2hhckNvZGU6IGZuLFxuICAgICAgZnJvbUNvZGVQb2ludDogZm4sXG4gICAgICBwcm90b3R5cGU6ICclU3RyaW5nUHJvdG90eXBlJScsXG4gICAgICByYXc6IGZuLFxuICAgICAgLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9Nb2RkYWJsZS1PcGVuU291cmNlL21vZGRhYmxlL2lzc3Vlcy81MjNcbiAgICAgIGZyb21BcnJheUJ1ZmZlcjogZmFsc2UsXG4gICAgfSxcblxuICAgICclU3RyaW5nUHJvdG90eXBlJSc6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIFN0cmluZyBQcm90b3R5cGUgT2JqZWN0XG4gICAgICBsZW5ndGg6ICdudW1iZXInLFxuICAgICAgY2hhckF0OiBmbixcbiAgICAgIGNoYXJDb2RlQXQ6IGZuLFxuICAgICAgY29kZVBvaW50QXQ6IGZuLFxuICAgICAgY29uY2F0OiBmbixcbiAgICAgIGNvbnN0cnVjdG9yOiAnU3RyaW5nJyxcbiAgICAgIGVuZHNXaXRoOiBmbixcbiAgICAgIGluY2x1ZGVzOiBmbixcbiAgICAgIGluZGV4T2Y6IGZuLFxuICAgICAgbGFzdEluZGV4T2Y6IGZuLFxuICAgICAgbG9jYWxlQ29tcGFyZTogZm4sXG4gICAgICBtYXRjaDogZm4sXG4gICAgICBtYXRjaEFsbDogZm4sXG4gICAgICBub3JtYWxpemU6IGZuLFxuICAgICAgcGFkRW5kOiBmbixcbiAgICAgIHBhZFN0YXJ0OiBmbixcbiAgICAgIHJlcGVhdDogZm4sXG4gICAgICByZXBsYWNlOiBmbixcbiAgICAgIHJlcGxhY2VBbGw6IGZuLCAvLyBFUzIwMjFcbiAgICAgIHNlYXJjaDogZm4sXG4gICAgICBzbGljZTogZm4sXG4gICAgICBzcGxpdDogZm4sXG4gICAgICBzdGFydHNXaXRoOiBmbixcbiAgICAgIHN1YnN0cmluZzogZm4sXG4gICAgICB0b0xvY2FsZUxvd2VyQ2FzZTogZm4sXG4gICAgICB0b0xvY2FsZVVwcGVyQ2FzZTogZm4sXG4gICAgICB0b0xvd2VyQ2FzZTogZm4sXG4gICAgICB0b1N0cmluZzogZm4sXG4gICAgICB0b1VwcGVyQ2FzZTogZm4sXG4gICAgICB0cmltOiBmbixcbiAgICAgIHRyaW1FbmQ6IGZuLFxuICAgICAgdHJpbVN0YXJ0OiBmbixcbiAgICAgIHZhbHVlT2Y6IGZuLFxuICAgICAgJ0BAaXRlcmF0b3InOiBmbixcblxuICAgICAgLy8gQW5uZXggQjogQWRkaXRpb25hbCBQcm9wZXJ0aWVzIG9mIHRoZSBTdHJpbmcucHJvdG90eXBlIE9iamVjdFxuICAgICAgc3Vic3RyOiBmbixcbiAgICAgIGFuY2hvcjogZm4sXG4gICAgICBiaWc6IGZuLFxuICAgICAgYmxpbms6IGZuLFxuICAgICAgYm9sZDogZm4sXG4gICAgICBmaXhlZDogZm4sXG4gICAgICBmb250Y29sb3I6IGZuLFxuICAgICAgZm9udHNpemU6IGZuLFxuICAgICAgaXRhbGljczogZm4sXG4gICAgICBsaW5rOiBmbixcbiAgICAgIHNtYWxsOiBmbixcbiAgICAgIHN0cmlrZTogZm4sXG4gICAgICBzdWI6IGZuLFxuICAgICAgc3VwOiBmbixcbiAgICAgIHRyaW1MZWZ0OiBmbixcbiAgICAgIHRyaW1SaWdodDogZm4sXG4gICAgICAvLyBTZWUgaHR0cHM6Ly9naXRodWIuY29tL01vZGRhYmxlLU9wZW5Tb3VyY2UvbW9kZGFibGUvaXNzdWVzLzUyM1xuICAgICAgY29tcGFyZTogZmFsc2UsXG4gICAgfSxcblxuICAgICclU3RyaW5nSXRlcmF0b3JQcm90b3R5cGUlJzoge1xuICAgICAgJ1tbUHJvdG9dXSc6ICclSXRlcmF0b3JQcm90b3R5cGUlJyxcbiAgICAgIG5leHQ6IGZuLFxuICAgICAgJ0BAdG9TdHJpbmdUYWcnOiAnc3RyaW5nJyxcbiAgICB9LFxuXG4gICAgJyVJbml0aWFsUmVnRXhwJSc6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIFJlZ0V4cCBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIHByb3RvdHlwZTogJyVSZWdFeHBQcm90b3R5cGUlJyxcbiAgICAgICdAQHNwZWNpZXMnOiBnZXR0ZXIsXG5cbiAgICAgIC8vIFRoZSBodHRwczovL2dpdGh1Yi5jb20vdGMzOS9wcm9wb3NhbC1yZWdleHAtbGVnYWN5LWZlYXR1cmVzXG4gICAgICAvLyBhcmUgYWxsIG9wdGlvbmFsLCB1bnNhZmUsIGFuZCBvbWl0dGVkXG4gICAgICBpbnB1dDogZmFsc2UsXG4gICAgICAkXzogZmFsc2UsXG4gICAgICBsYXN0TWF0Y2g6IGZhbHNlLFxuICAgICAgJyQmJzogZmFsc2UsXG4gICAgICBsYXN0UGFyZW46IGZhbHNlLFxuICAgICAgJyQrJzogZmFsc2UsXG4gICAgICBsZWZ0Q29udGV4dDogZmFsc2UsXG4gICAgICAnJGAnOiBmYWxzZSxcbiAgICAgIHJpZ2h0Q29udGV4dDogZmFsc2UsXG4gICAgICBcIiQnXCI6IGZhbHNlLFxuICAgICAgJDE6IGZhbHNlLFxuICAgICAgJDI6IGZhbHNlLFxuICAgICAgJDM6IGZhbHNlLFxuICAgICAgJDQ6IGZhbHNlLFxuICAgICAgJDU6IGZhbHNlLFxuICAgICAgJDY6IGZhbHNlLFxuICAgICAgJDc6IGZhbHNlLFxuICAgICAgJDg6IGZhbHNlLFxuICAgICAgJDk6IGZhbHNlLFxuICAgIH0sXG5cbiAgICAnJVNoYXJlZFJlZ0V4cCUnOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBSZWdFeHAgQ29uc3RydWN0b3JcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBwcm90b3R5cGU6ICclUmVnRXhwUHJvdG90eXBlJScsXG4gICAgICAnQEBzcGVjaWVzJzogZ2V0dGVyLFxuICAgIH0sXG5cbiAgICAnJVJlZ0V4cFByb3RvdHlwZSUnOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBSZWdFeHAgUHJvdG90eXBlIE9iamVjdFxuICAgICAgY29uc3RydWN0b3I6ICclU2hhcmVkUmVnRXhwJScsXG4gICAgICBleGVjOiBmbixcbiAgICAgIGRvdEFsbDogZ2V0dGVyLFxuICAgICAgZmxhZ3M6IGdldHRlcixcbiAgICAgIGdsb2JhbDogZ2V0dGVyLFxuICAgICAgaWdub3JlQ2FzZTogZ2V0dGVyLFxuICAgICAgJ0BAbWF0Y2gnOiBmbixcbiAgICAgICdAQG1hdGNoQWxsJzogZm4sXG4gICAgICBtdWx0aWxpbmU6IGdldHRlcixcbiAgICAgICdAQHJlcGxhY2UnOiBmbixcbiAgICAgICdAQHNlYXJjaCc6IGZuLFxuICAgICAgc291cmNlOiBnZXR0ZXIsXG4gICAgICAnQEBzcGxpdCc6IGZuLFxuICAgICAgc3RpY2t5OiBnZXR0ZXIsXG4gICAgICB0ZXN0OiBmbixcbiAgICAgIHRvU3RyaW5nOiBmbixcbiAgICAgIHVuaWNvZGU6IGdldHRlcixcblxuICAgICAgLy8gQW5uZXggQjogQWRkaXRpb25hbCBQcm9wZXJ0aWVzIG9mIHRoZSBSZWdFeHAucHJvdG90eXBlIE9iamVjdFxuICAgICAgY29tcGlsZTogZmFsc2UsIC8vIFVOU0FGRSBhbmQgc3VwcHJlc3NlZC5cbiAgICAgIC8vIFNlZW4gb24gRkYgTmlnaHRseSA4OC4wYTEsIENocm9tZSBDYW5hcnkgOTEuMC40NDQ2LjAsXG4gICAgICAvLyBTYWZhcmkgVGVjaCBQcmV2aWV3IFJlbGVhc2UgMTIyIChTYWZhcmkgMTQuMiwgV2ViS2l0IDE2NjEyLjEuNi4yKVxuICAgICAgaGFzSW5kaWNlczogZmFsc2UsXG4gICAgfSxcblxuICAgICclUmVnRXhwU3RyaW5nSXRlcmF0b3JQcm90b3R5cGUlJzoge1xuICAgICAgLy8gVGhlICVSZWdFeHBTdHJpbmdJdGVyYXRvclByb3RvdHlwZSUgT2JqZWN0XG4gICAgICAnW1tQcm90b11dJzogJyVJdGVyYXRvclByb3RvdHlwZSUnLFxuICAgICAgbmV4dDogZm4sXG4gICAgICAnQEB0b1N0cmluZ1RhZyc6ICdzdHJpbmcnLFxuICAgIH0sXG5cbiAgICAvLyBJbmRleGVkIENvbGxlY3Rpb25zXG5cbiAgICBBcnJheToge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgQXJyYXkgQ29uc3RydWN0b3JcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBmcm9tOiBmbixcbiAgICAgIGlzQXJyYXk6IGZuLFxuICAgICAgb2Y6IGZuLFxuICAgICAgcHJvdG90eXBlOiAnJUFycmF5UHJvdG90eXBlJScsXG4gICAgICAnQEBzcGVjaWVzJzogZ2V0dGVyLFxuICAgIH0sXG5cbiAgICAnJUFycmF5UHJvdG90eXBlJSc6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIEFycmF5IFByb3RvdHlwZSBPYmplY3RcbiAgICAgIGxlbmd0aDogJ251bWJlcicsXG4gICAgICBjb25jYXQ6IGZuLFxuICAgICAgY29uc3RydWN0b3I6ICdBcnJheScsXG4gICAgICBjb3B5V2l0aGluOiBmbixcbiAgICAgIGVudHJpZXM6IGZuLFxuICAgICAgZXZlcnk6IGZuLFxuICAgICAgZmlsbDogZm4sXG4gICAgICBmaWx0ZXI6IGZuLFxuICAgICAgZmluZDogZm4sXG4gICAgICBmaW5kSW5kZXg6IGZuLFxuICAgICAgZmxhdDogZm4sXG4gICAgICBmbGF0TWFwOiBmbixcbiAgICAgIGZvckVhY2g6IGZuLFxuICAgICAgaW5jbHVkZXM6IGZuLFxuICAgICAgaW5kZXhPZjogZm4sXG4gICAgICBqb2luOiBmbixcbiAgICAgIGtleXM6IGZuLFxuICAgICAgbGFzdEluZGV4T2Y6IGZuLFxuICAgICAgbWFwOiBmbixcbiAgICAgIHBvcDogZm4sXG4gICAgICBwdXNoOiBmbixcbiAgICAgIHJlZHVjZTogZm4sXG4gICAgICByZWR1Y2VSaWdodDogZm4sXG4gICAgICByZXZlcnNlOiBmbixcbiAgICAgIHNoaWZ0OiBmbixcbiAgICAgIHNsaWNlOiBmbixcbiAgICAgIHNvbWU6IGZuLFxuICAgICAgc29ydDogZm4sXG4gICAgICBzcGxpY2U6IGZuLFxuICAgICAgdG9Mb2NhbGVTdHJpbmc6IGZuLFxuICAgICAgdG9TdHJpbmc6IGZuLFxuICAgICAgdW5zaGlmdDogZm4sXG4gICAgICB2YWx1ZXM6IGZuLFxuICAgICAgJ0BAaXRlcmF0b3InOiBmbixcbiAgICAgICdAQHVuc2NvcGFibGVzJzoge1xuICAgICAgICAnW1tQcm90b11dJzogbnVsbCxcbiAgICAgICAgY29weVdpdGhpbjogJ2Jvb2xlYW4nLFxuICAgICAgICBlbnRyaWVzOiAnYm9vbGVhbicsXG4gICAgICAgIGZpbGw6ICdib29sZWFuJyxcbiAgICAgICAgZmluZDogJ2Jvb2xlYW4nLFxuICAgICAgICBmaW5kSW5kZXg6ICdib29sZWFuJyxcbiAgICAgICAgZmxhdDogJ2Jvb2xlYW4nLFxuICAgICAgICBmbGF0TWFwOiAnYm9vbGVhbicsXG4gICAgICAgIGluY2x1ZGVzOiAnYm9vbGVhbicsXG4gICAgICAgIGtleXM6ICdib29sZWFuJyxcbiAgICAgICAgdmFsdWVzOiAnYm9vbGVhbicsXG4gICAgICAgIC8vIEZhaWxlZCB0YzM5IHByb3Bvc2FsXG4gICAgICAgIC8vIFNlZW4gb24gRkYgTmlnaHRseSA4OC4wYTFcbiAgICAgICAgYXQ6IGZhbHNlLFxuICAgICAgfSxcbiAgICAgIC8vIEZhaWxlZCB0YzM5IHByb3Bvc2FsXG4gICAgICAvLyBTZWVuIG9uIEZGIE5pZ2h0bHkgODguMGExXG4gICAgICBhdDogZmFsc2UsXG4gICAgfSxcblxuICAgICclQXJyYXlJdGVyYXRvclByb3RvdHlwZSUnOiB7XG4gICAgICAvLyBUaGUgJUFycmF5SXRlcmF0b3JQcm90b3R5cGUlIE9iamVjdFxuICAgICAgJ1tbUHJvdG9dXSc6ICclSXRlcmF0b3JQcm90b3R5cGUlJyxcbiAgICAgIG5leHQ6IGZuLFxuICAgICAgJ0BAdG9TdHJpbmdUYWcnOiAnc3RyaW5nJyxcbiAgICB9LFxuXG4gICAgLy8gKioqIFR5cGVkQXJyYXkgT2JqZWN0c1xuXG4gICAgJyVUeXBlZEFycmF5JSc6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlICVUeXBlZEFycmF5JSBJbnRyaW5zaWMgT2JqZWN0XG4gICAgICAnW1tQcm90b11dJzogJyVGdW5jdGlvblByb3RvdHlwZSUnLFxuICAgICAgZnJvbTogZm4sXG4gICAgICBvZjogZm4sXG4gICAgICBwcm90b3R5cGU6ICclVHlwZWRBcnJheVByb3RvdHlwZSUnLFxuICAgICAgJ0BAc3BlY2llcyc6IGdldHRlcixcbiAgICB9LFxuXG4gICAgJyVUeXBlZEFycmF5UHJvdG90eXBlJSc6IHtcbiAgICAgIGJ1ZmZlcjogZ2V0dGVyLFxuICAgICAgYnl0ZUxlbmd0aDogZ2V0dGVyLFxuICAgICAgYnl0ZU9mZnNldDogZ2V0dGVyLFxuICAgICAgY29uc3RydWN0b3I6ICclVHlwZWRBcnJheSUnLFxuICAgICAgY29weVdpdGhpbjogZm4sXG4gICAgICBlbnRyaWVzOiBmbixcbiAgICAgIGV2ZXJ5OiBmbixcbiAgICAgIGZpbGw6IGZuLFxuICAgICAgZmlsdGVyOiBmbixcbiAgICAgIGZpbmQ6IGZuLFxuICAgICAgZmluZEluZGV4OiBmbixcbiAgICAgIGZvckVhY2g6IGZuLFxuICAgICAgaW5jbHVkZXM6IGZuLFxuICAgICAgaW5kZXhPZjogZm4sXG4gICAgICBqb2luOiBmbixcbiAgICAgIGtleXM6IGZuLFxuICAgICAgbGFzdEluZGV4T2Y6IGZuLFxuICAgICAgbGVuZ3RoOiBnZXR0ZXIsXG4gICAgICBtYXA6IGZuLFxuICAgICAgcmVkdWNlOiBmbixcbiAgICAgIHJlZHVjZVJpZ2h0OiBmbixcbiAgICAgIHJldmVyc2U6IGZuLFxuICAgICAgc2V0OiBmbixcbiAgICAgIHNsaWNlOiBmbixcbiAgICAgIHNvbWU6IGZuLFxuICAgICAgc29ydDogZm4sXG4gICAgICBzdWJhcnJheTogZm4sXG4gICAgICB0b0xvY2FsZVN0cmluZzogZm4sXG4gICAgICB0b1N0cmluZzogZm4sXG4gICAgICB2YWx1ZXM6IGZuLFxuICAgICAgJ0BAaXRlcmF0b3InOiBmbixcbiAgICAgICdAQHRvU3RyaW5nVGFnJzogZ2V0dGVyLFxuICAgICAgLy8gRmFpbGVkIHRjMzkgcHJvcG9zYWxcbiAgICAgIC8vIFNlZW4gb24gRkYgTmlnaHRseSA4OC4wYTFcbiAgICAgIGF0OiBmYWxzZSxcbiAgICB9LFxuXG4gICAgLy8gVGhlIFR5cGVkQXJyYXkgQ29uc3RydWN0b3JzXG5cbiAgICBCaWdJbnQ2NEFycmF5OiBUeXBlZEFycmF5KCclQmlnSW50NjRBcnJheVByb3RvdHlwZSUnKSxcbiAgICBCaWdVaW50NjRBcnJheTogVHlwZWRBcnJheSgnJUJpZ1VpbnQ2NEFycmF5UHJvdG90eXBlJScpLFxuICAgIEZsb2F0MzJBcnJheTogVHlwZWRBcnJheSgnJUZsb2F0MzJBcnJheVByb3RvdHlwZSUnKSxcbiAgICBGbG9hdDY0QXJyYXk6IFR5cGVkQXJyYXkoJyVGbG9hdDY0QXJyYXlQcm90b3R5cGUlJyksXG4gICAgSW50MTZBcnJheTogVHlwZWRBcnJheSgnJUludDE2QXJyYXlQcm90b3R5cGUlJyksXG4gICAgSW50MzJBcnJheTogVHlwZWRBcnJheSgnJUludDMyQXJyYXlQcm90b3R5cGUlJyksXG4gICAgSW50OEFycmF5OiBUeXBlZEFycmF5KCclSW50OEFycmF5UHJvdG90eXBlJScpLFxuICAgIFVpbnQxNkFycmF5OiBUeXBlZEFycmF5KCclVWludDE2QXJyYXlQcm90b3R5cGUlJyksXG4gICAgVWludDMyQXJyYXk6IFR5cGVkQXJyYXkoJyVVaW50MzJBcnJheVByb3RvdHlwZSUnKSxcbiAgICBVaW50OEFycmF5OiBUeXBlZEFycmF5KCclVWludDhBcnJheVByb3RvdHlwZSUnKSxcbiAgICBVaW50OENsYW1wZWRBcnJheTogVHlwZWRBcnJheSgnJVVpbnQ4Q2xhbXBlZEFycmF5UHJvdG90eXBlJScpLFxuXG4gICAgJyVCaWdJbnQ2NEFycmF5UHJvdG90eXBlJSc6IFR5cGVkQXJyYXlQcm90b3R5cGUoJ0JpZ0ludDY0QXJyYXknKSxcbiAgICAnJUJpZ1VpbnQ2NEFycmF5UHJvdG90eXBlJSc6IFR5cGVkQXJyYXlQcm90b3R5cGUoJ0JpZ1VpbnQ2NEFycmF5JyksXG4gICAgJyVGbG9hdDMyQXJyYXlQcm90b3R5cGUlJzogVHlwZWRBcnJheVByb3RvdHlwZSgnRmxvYXQzMkFycmF5JyksXG4gICAgJyVGbG9hdDY0QXJyYXlQcm90b3R5cGUlJzogVHlwZWRBcnJheVByb3RvdHlwZSgnRmxvYXQ2NEFycmF5JyksXG4gICAgJyVJbnQxNkFycmF5UHJvdG90eXBlJSc6IFR5cGVkQXJyYXlQcm90b3R5cGUoJ0ludDE2QXJyYXknKSxcbiAgICAnJUludDMyQXJyYXlQcm90b3R5cGUlJzogVHlwZWRBcnJheVByb3RvdHlwZSgnSW50MzJBcnJheScpLFxuICAgICclSW50OEFycmF5UHJvdG90eXBlJSc6IFR5cGVkQXJyYXlQcm90b3R5cGUoJ0ludDhBcnJheScpLFxuICAgICclVWludDE2QXJyYXlQcm90b3R5cGUlJzogVHlwZWRBcnJheVByb3RvdHlwZSgnVWludDE2QXJyYXknKSxcbiAgICAnJVVpbnQzMkFycmF5UHJvdG90eXBlJSc6IFR5cGVkQXJyYXlQcm90b3R5cGUoJ1VpbnQzMkFycmF5JyksXG4gICAgJyVVaW50OEFycmF5UHJvdG90eXBlJSc6IFR5cGVkQXJyYXlQcm90b3R5cGUoJ1VpbnQ4QXJyYXknKSxcbiAgICAnJVVpbnQ4Q2xhbXBlZEFycmF5UHJvdG90eXBlJSc6IFR5cGVkQXJyYXlQcm90b3R5cGUoJ1VpbnQ4Q2xhbXBlZEFycmF5JyksXG5cbiAgICAvLyAqKiogS2V5ZWQgQ29sbGVjdGlvbnNcblxuICAgIE1hcDoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgTWFwIENvbnN0cnVjdG9yXG4gICAgICAnW1tQcm90b11dJzogJyVGdW5jdGlvblByb3RvdHlwZSUnLFxuICAgICAgJ0BAc3BlY2llcyc6IGdldHRlcixcbiAgICAgIHByb3RvdHlwZTogJyVNYXBQcm90b3R5cGUlJyxcbiAgICB9LFxuXG4gICAgJyVNYXBQcm90b3R5cGUlJzoge1xuICAgICAgY2xlYXI6IGZuLFxuICAgICAgY29uc3RydWN0b3I6ICdNYXAnLFxuICAgICAgZGVsZXRlOiBmbixcbiAgICAgIGVudHJpZXM6IGZuLFxuICAgICAgZm9yRWFjaDogZm4sXG4gICAgICBnZXQ6IGZuLFxuICAgICAgaGFzOiBmbixcbiAgICAgIGtleXM6IGZuLFxuICAgICAgc2V0OiBmbixcbiAgICAgIHNpemU6IGdldHRlcixcbiAgICAgIHZhbHVlczogZm4sXG4gICAgICAnQEBpdGVyYXRvcic6IGZuLFxuICAgICAgJ0BAdG9TdHJpbmdUYWcnOiAnc3RyaW5nJyxcbiAgICB9LFxuXG4gICAgJyVNYXBJdGVyYXRvclByb3RvdHlwZSUnOiB7XG4gICAgICAvLyBUaGUgJU1hcEl0ZXJhdG9yUHJvdG90eXBlJSBPYmplY3RcbiAgICAgICdbW1Byb3RvXV0nOiAnJUl0ZXJhdG9yUHJvdG90eXBlJScsXG4gICAgICBuZXh0OiBmbixcbiAgICAgICdAQHRvU3RyaW5nVGFnJzogJ3N0cmluZycsXG4gICAgfSxcblxuICAgIFNldDoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgU2V0IENvbnN0cnVjdG9yXG4gICAgICAnW1tQcm90b11dJzogJyVGdW5jdGlvblByb3RvdHlwZSUnLFxuICAgICAgcHJvdG90eXBlOiAnJVNldFByb3RvdHlwZSUnLFxuICAgICAgJ0BAc3BlY2llcyc6IGdldHRlcixcbiAgICB9LFxuXG4gICAgJyVTZXRQcm90b3R5cGUlJzoge1xuICAgICAgYWRkOiBmbixcbiAgICAgIGNsZWFyOiBmbixcbiAgICAgIGNvbnN0cnVjdG9yOiAnU2V0JyxcbiAgICAgIGRlbGV0ZTogZm4sXG4gICAgICBlbnRyaWVzOiBmbixcbiAgICAgIGZvckVhY2g6IGZuLFxuICAgICAgaGFzOiBmbixcbiAgICAgIGtleXM6IGZuLFxuICAgICAgc2l6ZTogZ2V0dGVyLFxuICAgICAgdmFsdWVzOiBmbixcbiAgICAgICdAQGl0ZXJhdG9yJzogZm4sXG4gICAgICAnQEB0b1N0cmluZ1RhZyc6ICdzdHJpbmcnLFxuICAgIH0sXG5cbiAgICAnJVNldEl0ZXJhdG9yUHJvdG90eXBlJSc6IHtcbiAgICAgIC8vIFRoZSAlU2V0SXRlcmF0b3JQcm90b3R5cGUlIE9iamVjdFxuICAgICAgJ1tbUHJvdG9dXSc6ICclSXRlcmF0b3JQcm90b3R5cGUlJyxcbiAgICAgIG5leHQ6IGZuLFxuICAgICAgJ0BAdG9TdHJpbmdUYWcnOiAnc3RyaW5nJyxcbiAgICB9LFxuXG4gICAgV2Vha01hcDoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgV2Vha01hcCBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIHByb3RvdHlwZTogJyVXZWFrTWFwUHJvdG90eXBlJScsXG4gICAgfSxcblxuICAgICclV2Vha01hcFByb3RvdHlwZSUnOiB7XG4gICAgICBjb25zdHJ1Y3RvcjogJ1dlYWtNYXAnLFxuICAgICAgZGVsZXRlOiBmbixcbiAgICAgIGdldDogZm4sXG4gICAgICBoYXM6IGZuLFxuICAgICAgc2V0OiBmbixcbiAgICAgICdAQHRvU3RyaW5nVGFnJzogJ3N0cmluZycsXG4gICAgfSxcblxuICAgIFdlYWtTZXQ6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIFdlYWtTZXQgQ29uc3RydWN0b3JcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBwcm90b3R5cGU6ICclV2Vha1NldFByb3RvdHlwZSUnLFxuICAgIH0sXG5cbiAgICAnJVdlYWtTZXRQcm90b3R5cGUlJzoge1xuICAgICAgYWRkOiBmbixcbiAgICAgIGNvbnN0cnVjdG9yOiAnV2Vha1NldCcsXG4gICAgICBkZWxldGU6IGZuLFxuICAgICAgaGFzOiBmbixcbiAgICAgICdAQHRvU3RyaW5nVGFnJzogJ3N0cmluZycsXG4gICAgfSxcblxuICAgIC8vICoqKiBTdHJ1Y3R1cmVkIERhdGFcblxuICAgIEFycmF5QnVmZmVyOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBBcnJheUJ1ZmZlciBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIGlzVmlldzogZm4sXG4gICAgICBwcm90b3R5cGU6ICclQXJyYXlCdWZmZXJQcm90b3R5cGUlJyxcbiAgICAgICdAQHNwZWNpZXMnOiBnZXR0ZXIsXG4gICAgICAvLyBTZWUgaHR0cHM6Ly9naXRodWIuY29tL01vZGRhYmxlLU9wZW5Tb3VyY2UvbW9kZGFibGUvaXNzdWVzLzUyM1xuICAgICAgZnJvbVN0cmluZzogZmFsc2UsXG4gICAgICAvLyBTZWUgaHR0cHM6Ly9naXRodWIuY29tL01vZGRhYmxlLU9wZW5Tb3VyY2UvbW9kZGFibGUvaXNzdWVzLzUyM1xuICAgICAgZnJvbUJpZ0ludDogZmFsc2UsXG4gICAgfSxcblxuICAgICclQXJyYXlCdWZmZXJQcm90b3R5cGUlJzoge1xuICAgICAgYnl0ZUxlbmd0aDogZ2V0dGVyLFxuICAgICAgY29uc3RydWN0b3I6ICdBcnJheUJ1ZmZlcicsXG4gICAgICBzbGljZTogZm4sXG4gICAgICAnQEB0b1N0cmluZ1RhZyc6ICdzdHJpbmcnLFxuICAgICAgLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9Nb2RkYWJsZS1PcGVuU291cmNlL21vZGRhYmxlL2lzc3Vlcy81MjNcbiAgICAgIGNvbmNhdDogZmFsc2UsXG4gICAgfSxcblxuICAgIC8vIFNoYXJlZEFycmF5QnVmZmVyIE9iamVjdHNcbiAgICBTaGFyZWRBcnJheUJ1ZmZlcjogZmFsc2UsIC8vIFVOU0FGRSBhbmQgcHVycG9zZWx5IHN1cHByZXNzZWQuXG4gICAgJyVTaGFyZWRBcnJheUJ1ZmZlclByb3RvdHlwZSUnOiBmYWxzZSwgLy8gVU5TQUZFIGFuZCBwdXJwb3NlbHkgc3VwcHJlc3NlZC5cblxuICAgIERhdGFWaWV3OiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBEYXRhVmlldyBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIEJZVEVTX1BFUl9FTEVNRU5UOiAnbnVtYmVyJywgLy8gTm9uIHN0ZCBidXQgdW5kZWxldGFibGUgb24gU2FmYXJpLlxuICAgICAgcHJvdG90eXBlOiAnJURhdGFWaWV3UHJvdG90eXBlJScsXG4gICAgfSxcblxuICAgICclRGF0YVZpZXdQcm90b3R5cGUlJzoge1xuICAgICAgYnVmZmVyOiBnZXR0ZXIsXG4gICAgICBieXRlTGVuZ3RoOiBnZXR0ZXIsXG4gICAgICBieXRlT2Zmc2V0OiBnZXR0ZXIsXG4gICAgICBjb25zdHJ1Y3RvcjogJ0RhdGFWaWV3JyxcbiAgICAgIGdldEJpZ0ludDY0OiBmbixcbiAgICAgIGdldEJpZ1VpbnQ2NDogZm4sXG4gICAgICBnZXRGbG9hdDMyOiBmbixcbiAgICAgIGdldEZsb2F0NjQ6IGZuLFxuICAgICAgZ2V0SW50ODogZm4sXG4gICAgICBnZXRJbnQxNjogZm4sXG4gICAgICBnZXRJbnQzMjogZm4sXG4gICAgICBnZXRVaW50ODogZm4sXG4gICAgICBnZXRVaW50MTY6IGZuLFxuICAgICAgZ2V0VWludDMyOiBmbixcbiAgICAgIHNldEJpZ0ludDY0OiBmbixcbiAgICAgIHNldEJpZ1VpbnQ2NDogZm4sXG4gICAgICBzZXRGbG9hdDMyOiBmbixcbiAgICAgIHNldEZsb2F0NjQ6IGZuLFxuICAgICAgc2V0SW50ODogZm4sXG4gICAgICBzZXRJbnQxNjogZm4sXG4gICAgICBzZXRJbnQzMjogZm4sXG4gICAgICBzZXRVaW50ODogZm4sXG4gICAgICBzZXRVaW50MTY6IGZuLFxuICAgICAgc2V0VWludDMyOiBmbixcbiAgICAgICdAQHRvU3RyaW5nVGFnJzogJ3N0cmluZycsXG4gICAgfSxcblxuICAgIC8vIEF0b21pY3NcbiAgICBBdG9taWNzOiBmYWxzZSwgLy8gVU5TQUZFIGFuZCBzdXBwcmVzc2VkLlxuXG4gICAgSlNPTjoge1xuICAgICAgcGFyc2U6IGZuLFxuICAgICAgc3RyaW5naWZ5OiBmbixcbiAgICAgICdAQHRvU3RyaW5nVGFnJzogJ3N0cmluZycsXG4gICAgfSxcblxuICAgIC8vICoqKiBDb250cm9sIEFic3RyYWN0aW9uIE9iamVjdHNcblxuICAgICclSXRlcmF0b3JQcm90b3R5cGUlJzoge1xuICAgICAgLy8gVGhlICVJdGVyYXRvclByb3RvdHlwZSUgT2JqZWN0XG4gICAgICAnQEBpdGVyYXRvcic6IGZuLFxuICAgIH0sXG5cbiAgICAnJUFzeW5jSXRlcmF0b3JQcm90b3R5cGUlJzoge1xuICAgICAgLy8gVGhlICVBc3luY0l0ZXJhdG9yUHJvdG90eXBlJSBPYmplY3RcbiAgICAgICdAQGFzeW5jSXRlcmF0b3InOiBmbixcbiAgICB9LFxuXG4gICAgJyVJbmVydEdlbmVyYXRvckZ1bmN0aW9uJSc6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIEdlbmVyYXRvckZ1bmN0aW9uIENvbnN0cnVjdG9yXG4gICAgICAnW1tQcm90b11dJzogJyVJbmVydEZ1bmN0aW9uJScsXG4gICAgICBwcm90b3R5cGU6ICclR2VuZXJhdG9yJScsXG4gICAgfSxcblxuICAgICclR2VuZXJhdG9yJSc6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIEdlbmVyYXRvckZ1bmN0aW9uIFByb3RvdHlwZSBPYmplY3RcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBjb25zdHJ1Y3RvcjogJyVJbmVydEdlbmVyYXRvckZ1bmN0aW9uJScsXG4gICAgICBwcm90b3R5cGU6ICclR2VuZXJhdG9yUHJvdG90eXBlJScsXG4gICAgICAnQEB0b1N0cmluZ1RhZyc6ICdzdHJpbmcnLFxuICAgIH0sXG5cbiAgICAnJUluZXJ0QXN5bmNHZW5lcmF0b3JGdW5jdGlvbiUnOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBBc3luY0dlbmVyYXRvckZ1bmN0aW9uIENvbnN0cnVjdG9yXG4gICAgICAnW1tQcm90b11dJzogJyVJbmVydEZ1bmN0aW9uJScsXG4gICAgICBwcm90b3R5cGU6ICclQXN5bmNHZW5lcmF0b3IlJyxcbiAgICB9LFxuXG4gICAgJyVBc3luY0dlbmVyYXRvciUnOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBBc3luY0dlbmVyYXRvckZ1bmN0aW9uIFByb3RvdHlwZSBPYmplY3RcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBjb25zdHJ1Y3RvcjogJyVJbmVydEFzeW5jR2VuZXJhdG9yRnVuY3Rpb24lJyxcbiAgICAgIHByb3RvdHlwZTogJyVBc3luY0dlbmVyYXRvclByb3RvdHlwZSUnLFxuICAgICAgJ0BAdG9TdHJpbmdUYWcnOiAnc3RyaW5nJyxcbiAgICB9LFxuXG4gICAgJyVHZW5lcmF0b3JQcm90b3R5cGUlJzoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgR2VuZXJhdG9yIFByb3RvdHlwZSBPYmplY3RcbiAgICAgICdbW1Byb3RvXV0nOiAnJUl0ZXJhdG9yUHJvdG90eXBlJScsXG4gICAgICBjb25zdHJ1Y3RvcjogJyVHZW5lcmF0b3IlJyxcbiAgICAgIG5leHQ6IGZuLFxuICAgICAgcmV0dXJuOiBmbixcbiAgICAgIHRocm93OiBmbixcbiAgICAgICdAQHRvU3RyaW5nVGFnJzogJ3N0cmluZycsXG4gICAgfSxcblxuICAgICclQXN5bmNHZW5lcmF0b3JQcm90b3R5cGUlJzoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgQXN5bmNHZW5lcmF0b3IgUHJvdG90eXBlIE9iamVjdFxuICAgICAgJ1tbUHJvdG9dXSc6ICclQXN5bmNJdGVyYXRvclByb3RvdHlwZSUnLFxuICAgICAgY29uc3RydWN0b3I6ICclQXN5bmNHZW5lcmF0b3IlJyxcbiAgICAgIG5leHQ6IGZuLFxuICAgICAgcmV0dXJuOiBmbixcbiAgICAgIHRocm93OiBmbixcbiAgICAgICdAQHRvU3RyaW5nVGFnJzogJ3N0cmluZycsXG4gICAgfSxcblxuICAgIC8vIFRPRE86IFRvIGJlIHJlcGxhY2VkIHdpdGggUHJvbWlzZS5kZWxlZ2F0ZVxuICAgIC8vXG4gICAgLy8gVGhlIEhhbmRsZWRQcm9taXNlIGdsb2JhbCB2YXJpYWJsZSBzaGltbWVkIGJ5IGBAYWdvcmljL2V2ZW50dWFsLXNlbmQvc2hpbWBcbiAgICAvLyBpbXBsZW1lbnRzIGFuIGluaXRpYWwgdmVyc2lvbiBvZiB0aGUgZXZlbnR1YWwgc2VuZCBzcGVjaWZpY2F0aW9uIGF0OlxuICAgIC8vIGh0dHBzOi8vZ2l0aHViLmNvbS90YzM5L3Byb3Bvc2FsLWV2ZW50dWFsLXNlbmRcbiAgICAvL1xuICAgIC8vIFdlIHdpbGwgbGlrZWx5IGNoYW5nZSB0aGlzIHRvIGFkZCBhIHByb3BlcnR5IHRvIFByb21pc2UgY2FsbGVkXG4gICAgLy8gUHJvbWlzZS5kZWxlZ2F0ZSBhbmQgcHV0IHN0YXRpYyBtZXRob2RzIG9uIGl0LCB3aGljaCB3aWxsIG5lY2Vzc2l0YXRlXG4gICAgLy8gYW5vdGhlciB3aGl0ZWxpc3QgY2hhbmdlIHRvIHVwZGF0ZSB0byB0aGUgY3VycmVudCBwcm9wb3NlZCBzdGFuZGFyZC5cbiAgICBIYW5kbGVkUHJvbWlzZToge1xuICAgICAgJ1tbUHJvdG9dXSc6ICdQcm9taXNlJyxcbiAgICAgIGFwcGx5RnVuY3Rpb246IGZuLFxuICAgICAgYXBwbHlGdW5jdGlvblNlbmRPbmx5OiBmbixcbiAgICAgIGFwcGx5TWV0aG9kOiBmbixcbiAgICAgIGFwcGx5TWV0aG9kU2VuZE9ubHk6IGZuLFxuICAgICAgZ2V0OiBmbixcbiAgICAgIGdldFNlbmRPbmx5OiBmbixcbiAgICAgIHByb3RvdHlwZTogJyVQcm9taXNlUHJvdG90eXBlJScsXG4gICAgICByZXNvbHZlOiBmbixcbiAgICB9LFxuXG4gICAgUHJvbWlzZToge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgUHJvbWlzZSBDb25zdHJ1Y3RvclxuICAgICAgJ1tbUHJvdG9dXSc6ICclRnVuY3Rpb25Qcm90b3R5cGUlJyxcbiAgICAgIGFsbDogZm4sXG4gICAgICBhbGxTZXR0bGVkOiBmbixcbiAgICAgIC8vIFRvIHRyYW5zaXRpb24gZnJvbSBgZmFsc2VgIHRvIGBmbmAgb25jZSB3ZSBhbHNvIGhhdmUgYEFnZ3JlZ2F0ZUVycm9yYFxuICAgICAgLy8gVE9ETyBodHRwczovL2dpdGh1Yi5jb20vQWdvcmljL1NFUy1zaGltL2lzc3Vlcy81NTBcbiAgICAgIGFueTogZmFsc2UsIC8vIEVTMjAyMVxuICAgICAgcHJvdG90eXBlOiAnJVByb21pc2VQcm90b3R5cGUlJyxcbiAgICAgIHJhY2U6IGZuLFxuICAgICAgcmVqZWN0OiBmbixcbiAgICAgIHJlc29sdmU6IGZuLFxuICAgICAgJ0BAc3BlY2llcyc6IGdldHRlcixcbiAgICB9LFxuXG4gICAgJyVQcm9taXNlUHJvdG90eXBlJSc6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIFByb21pc2UgUHJvdG90eXBlIE9iamVjdFxuICAgICAgY2F0Y2g6IGZuLFxuICAgICAgY29uc3RydWN0b3I6ICdQcm9taXNlJyxcbiAgICAgIGZpbmFsbHk6IGZuLFxuICAgICAgdGhlbjogZm4sXG4gICAgICAnQEB0b1N0cmluZ1RhZyc6ICdzdHJpbmcnLFxuICAgIH0sXG5cbiAgICAnJUluZXJ0QXN5bmNGdW5jdGlvbiUnOiB7XG4gICAgICAvLyBQcm9wZXJ0aWVzIG9mIHRoZSBBc3luY0Z1bmN0aW9uIENvbnN0cnVjdG9yXG4gICAgICAnW1tQcm90b11dJzogJyVJbmVydEZ1bmN0aW9uJScsXG4gICAgICBwcm90b3R5cGU6ICclQXN5bmNGdW5jdGlvblByb3RvdHlwZSUnLFxuICAgIH0sXG5cbiAgICAnJUFzeW5jRnVuY3Rpb25Qcm90b3R5cGUlJzoge1xuICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgQXN5bmNGdW5jdGlvbiBQcm90b3R5cGUgT2JqZWN0XG4gICAgICAnW1tQcm90b11dJzogJyVGdW5jdGlvblByb3RvdHlwZSUnLFxuICAgICAgY29uc3RydWN0b3I6ICclSW5lcnRBc3luY0Z1bmN0aW9uJScsXG4gICAgICAnQEB0b1N0cmluZ1RhZyc6ICdzdHJpbmcnLFxuICAgIH0sXG5cbiAgICAvLyBSZWZsZWN0aW9uXG5cbiAgICBSZWZsZWN0OiB7XG4gICAgICAvLyBUaGUgUmVmbGVjdCBPYmplY3RcbiAgICAgIC8vIE5vdCBhIGZ1bmN0aW9uIG9iamVjdC5cbiAgICAgIGFwcGx5OiBmbixcbiAgICAgIGNvbnN0cnVjdDogZm4sXG4gICAgICBkZWZpbmVQcm9wZXJ0eTogZm4sXG4gICAgICBkZWxldGVQcm9wZXJ0eTogZm4sXG4gICAgICBnZXQ6IGZuLFxuICAgICAgZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yOiBmbixcbiAgICAgIGdldFByb3RvdHlwZU9mOiBmbixcbiAgICAgIGhhczogZm4sXG4gICAgICBpc0V4dGVuc2libGU6IGZuLFxuICAgICAgb3duS2V5czogZm4sXG4gICAgICBwcmV2ZW50RXh0ZW5zaW9uczogZm4sXG4gICAgICBzZXQ6IGZuLFxuICAgICAgc2V0UHJvdG90eXBlT2Y6IGZuLFxuICAgICAgJ0BAdG9TdHJpbmdUYWcnOiAnc3RyaW5nJyxcbiAgICB9LFxuXG4gICAgUHJveHk6IHtcbiAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIFByb3h5IENvbnN0cnVjdG9yXG4gICAgICAnW1tQcm90b11dJzogJyVGdW5jdGlvblByb3RvdHlwZSUnLFxuICAgICAgcmV2b2NhYmxlOiBmbixcbiAgICB9LFxuXG4gICAgLy8gQXBwZW5kaXggQlxuXG4gICAgLy8gQW5uZXggQjogQWRkaXRpb25hbCBQcm9wZXJ0aWVzIG9mIHRoZSBHbG9iYWwgT2JqZWN0XG5cbiAgICBlc2NhcGU6IGZuLFxuICAgIHVuZXNjYXBlOiBmbixcblxuICAgIC8vIFByb3Bvc2VkXG5cbiAgICAnJVVuaXF1ZUNvbXBhcnRtZW50JSc6IHtcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBwcm90b3R5cGU6ICclQ29tcGFydG1lbnRQcm90b3R5cGUlJyxcbiAgICAgIHRvU3RyaW5nOiBmbixcbiAgICB9LFxuXG4gICAgJyVJbmVydENvbXBhcnRtZW50JSc6IHtcbiAgICAgICdbW1Byb3RvXV0nOiAnJUZ1bmN0aW9uUHJvdG90eXBlJScsXG4gICAgICBwcm90b3R5cGU6ICclQ29tcGFydG1lbnRQcm90b3R5cGUlJyxcbiAgICAgIHRvU3RyaW5nOiBmbixcbiAgICB9LFxuXG4gICAgJyVDb21wYXJ0bWVudFByb3RvdHlwZSUnOiB7XG4gICAgICBjb25zdHJ1Y3RvcjogJyVJbmVydENvbXBhcnRtZW50JScsXG4gICAgICBldmFsdWF0ZTogZm4sXG4gICAgICBnbG9iYWxUaGlzOiBnZXR0ZXIsXG4gICAgICBuYW1lOiBnZXR0ZXIsXG4gICAgICAvLyBTaG91bGQgdGhpcyBiZSBwcm9wb3NlZD9cbiAgICAgIHRvU3RyaW5nOiBmbixcbiAgICAgIF9faXNLbm93blNjb3BlUHJveHlfXzogZm4sXG4gICAgfSxcblxuICAgIGxvY2tkb3duOiBmbixcbiAgICBoYXJkZW46IGZuLFxuXG4gICAgJyVJbml0aWFsR2V0U3RhY2tTdHJpbmclJzogZm4sXG4gIH07XG5cbiAgLy8gTGlrZSBkZWZpbmVQcm9wZXJ0eSwgYnV0IHRocm93cyBpZiBpdCB3b3VsZCBtb2RpZnkgYW4gZXhpc3RpbmcgcHJvcGVydHkuXG4gIC8vIFdlIHVzZSB0aGlzIHRvIGVuc3VyZSB0aGF0IHR3byBjb25mbGljdGluZyBhdHRlbXB0cyB0byBkZWZpbmUgdGhlIHNhbWVcbiAgLy8gcHJvcGVydHkgdGhyb3dzLCBjYXVzaW5nIFNFUyBpbml0aWFsaXphdGlvbiB0byBmYWlsLiBPdGhlcndpc2UsIGFcbiAgLy8gY29uZmxpY3QgYmV0d2VlbiwgZm9yIGV4YW1wbGUsIHR3byBvZiBTRVMncyBpbnRlcm5hbCB3aGl0ZWxpc3RzIG1pZ2h0XG4gIC8vIGdldCBtYXNrZWQgYXMgb25lIG92ZXJ3cml0ZXMgdGhlIG90aGVyLiBBY2NvcmRpbmdseSwgdGhlIHRocm93biBlcnJvclxuICAvLyBjb21wbGFpbnMgb2YgYSBcIkNvbmZsaWN0aW5nIGRlZmluaXRpb25cIi5cbiAgZnVuY3Rpb24gaW5pdFByb3BlcnR5KG9iaiwgbmFtZSwgZGVzYykge1xuICAgIGlmIChvYmplY3RIYXNPd25Qcm9wZXJ0eShvYmosIG5hbWUpKSB7XG4gICAgICBjb25zdCBwcmVEZXNjID0gZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKG9iaiwgbmFtZSk7XG4gICAgICBpZiAoXG4gICAgICAgICFPYmplY3QuaXMocHJlRGVzYy52YWx1ZSwgZGVzYy52YWx1ZSkgfHxcbiAgICAgICAgcHJlRGVzYy5nZXQgIT09IGRlc2MuZ2V0IHx8XG4gICAgICAgIHByZURlc2Muc2V0ICE9PSBkZXNjLnNldCB8fFxuICAgICAgICBwcmVEZXNjLndyaXRhYmxlICE9PSBkZXNjLndyaXRhYmxlIHx8XG4gICAgICAgIHByZURlc2MuZW51bWVyYWJsZSAhPT0gZGVzYy5lbnVtZXJhYmxlIHx8XG4gICAgICAgIHByZURlc2MuY29uZmlndXJhYmxlICE9PSBkZXNjLmNvbmZpZ3VyYWJsZVxuICAgICAgKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcihgQ29uZmxpY3RpbmcgZGVmaW5pdGlvbnMgb2YgJHtuYW1lfWApO1xuICAgICAgfVxuICAgIH1cbiAgICBkZWZpbmVQcm9wZXJ0eShvYmosIG5hbWUsIGRlc2MpO1xuICB9XG5cbiAgLy8gTGlrZSBkZWZpbmVQcm9wZXJ0aWVzLCBidXQgdGhyb3dzIGlmIGl0IHdvdWxkIG1vZGlmeSBhbiBleGlzdGluZyBwcm9wZXJ0eS5cbiAgLy8gVGhpcyBlbnN1cmVzIHRoYXQgdGhlIGludHJpbnNpY3MgYWRkZWQgdG8gdGhlIGludHJpbnNpY3MgY29sbGVjdG9yIG9iamVjdFxuICAvLyBncmFwaCBkbyBub3Qgb3ZlcmxhcC5cbiAgZnVuY3Rpb24gaW5pdFByb3BlcnRpZXMob2JqLCBkZXNjcykge1xuICAgIGZvciAoY29uc3QgW25hbWUsIGRlc2NdIG9mIGVudHJpZXMoZGVzY3MpKSB7XG4gICAgICBpbml0UHJvcGVydHkob2JqLCBuYW1lLCBkZXNjKTtcbiAgICB9XG4gIH1cblxuICAvLyBzYW1wbGVHbG9iYWxzIGNyZWF0ZXMgYW4gaW50cmluc2ljcyBvYmplY3QsIHN1aXRhYmxlIGZvclxuICAvLyBpbnRlcmluc2ljc0NvbGxlY3Rvci5hZGRJbnRyaW5zaWNzLCBmcm9tIHRoZSBuYW1lZCBwcm9wZXJ0aWVzIG9mIGEgZ2xvYmFsXG4gIC8vIG9iamVjdC5cbiAgZnVuY3Rpb24gc2FtcGxlR2xvYmFscyhnbG9iYWxPYmplY3QsIG5ld1Byb3BlcnR5TmFtZXMpIHtcbiAgICBjb25zdCBuZXdJbnRyaW5zaWNzID0geyBfX3Byb3RvX186IG51bGwgfTtcbiAgICBmb3IgKGNvbnN0IFtnbG9iYWxOYW1lLCBpbnRyaW5zaWNOYW1lXSBvZiBlbnRyaWVzKG5ld1Byb3BlcnR5TmFtZXMpKSB7XG4gICAgICBpZiAob2JqZWN0SGFzT3duUHJvcGVydHkoZ2xvYmFsT2JqZWN0LCBnbG9iYWxOYW1lKSkge1xuICAgICAgICBuZXdJbnRyaW5zaWNzW2ludHJpbnNpY05hbWVdID0gZ2xvYmFsT2JqZWN0W2dsb2JhbE5hbWVdO1xuICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gbmV3SW50cmluc2ljcztcbiAgfVxuXG4gIGZ1bmN0aW9uIG1ha2VJbnRyaW5zaWNzQ29sbGVjdG9yKCkge1xuICAgIGNvbnN0IGludHJpbnNpY3MgPSB7IF9fcHJvdG9fXzogbnVsbCB9O1xuICAgIGxldCBwc2V1ZG9OYXRpdmVzO1xuXG4gICAgY29uc3QgaW50cmluc2ljc0NvbGxlY3RvciA9IHtcbiAgICAgIGFkZEludHJpbnNpY3MobmV3SW50cmluc2ljcykge1xuICAgICAgICBpbml0UHJvcGVydGllcyhpbnRyaW5zaWNzLCBnZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3JzKG5ld0ludHJpbnNpY3MpKTtcbiAgICAgIH0sXG5cbiAgICAgIC8vIEZvciBlYWNoIGludHJpbnNpYywgaWYgaXQgaGFzIGEgYC5wcm90b3R5cGVgIHByb3BlcnR5LCB1c2UgdGhlXG4gICAgICAvLyB3aGl0ZWxpc3QgdG8gZmluZCBvdXQgdGhlIGludHJpbnNpYyBuYW1lIGZvciB0aGF0IHByb3RvdHlwZSBhbmQgYWRkIGl0XG4gICAgICAvLyB0byB0aGUgaW50cmluc2ljcy5cbiAgICAgIGNvbXBsZXRlUHJvdG90eXBlcygpIHtcbiAgICAgICAgZm9yIChjb25zdCBbbmFtZSwgaW50cmluc2ljXSBvZiBlbnRyaWVzKGludHJpbnNpY3MpKSB7XG4gICAgICAgICAgaWYgKGludHJpbnNpYyAhPT0gT2JqZWN0KGludHJpbnNpYykpIHtcbiAgICAgICAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1jb250aW51ZVxuICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgICAgfVxuICAgICAgICAgIGlmICghb2JqZWN0SGFzT3duUHJvcGVydHkoaW50cmluc2ljLCAncHJvdG90eXBlJykpIHtcbiAgICAgICAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1jb250aW51ZVxuICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgICAgfVxuICAgICAgICAgIGNvbnN0IHBlcm1pdCA9IHdoaXRlbGlzdFtuYW1lXTtcbiAgICAgICAgICBpZiAodHlwZW9mIHBlcm1pdCAhPT0gJ29iamVjdCcpIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcihgRXhwZWN0ZWQgcGVybWl0IG9iamVjdCBhdCB3aGl0ZWxpc3QuJHtuYW1lfWApO1xuICAgICAgICAgIH1cbiAgICAgICAgICBjb25zdCBuYW1lUHJvdG90eXBlID0gcGVybWl0LnByb3RvdHlwZTtcbiAgICAgICAgICBpZiAoIW5hbWVQcm90b3R5cGUpIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcihgJHtuYW1lfS5wcm90b3R5cGUgcHJvcGVydHkgbm90IHdoaXRlbGlzdGVkYCk7XG4gICAgICAgICAgfVxuICAgICAgICAgIGlmIChcbiAgICAgICAgICAgIHR5cGVvZiBuYW1lUHJvdG90eXBlICE9PSAnc3RyaW5nJyB8fFxuICAgICAgICAgICAgIW9iamVjdEhhc093blByb3BlcnR5KHdoaXRlbGlzdCwgbmFtZVByb3RvdHlwZSlcbiAgICAgICAgICApIHtcbiAgICAgICAgICAgIHRocm93IG5ldyBFcnJvcihgVW5yZWNvZ25pemVkICR7bmFtZX0ucHJvdG90eXBlIHdoaXRlbGlzdCBlbnRyeWApO1xuICAgICAgICAgIH1cbiAgICAgICAgICBjb25zdCBpbnRyaW5zaWNQcm90b3R5cGUgPSBpbnRyaW5zaWMucHJvdG90eXBlO1xuICAgICAgICAgIGlmIChvYmplY3RIYXNPd25Qcm9wZXJ0eShpbnRyaW5zaWNzLCBuYW1lUHJvdG90eXBlKSkge1xuICAgICAgICAgICAgaWYgKGludHJpbnNpY3NbbmFtZVByb3RvdHlwZV0gIT09IGludHJpbnNpY1Byb3RvdHlwZSkge1xuICAgICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoYENvbmZsaWN0aW5nIGJpbmRpbmdzIG9mICR7bmFtZVByb3RvdHlwZX1gKTtcbiAgICAgICAgICAgIH1cbiAgICAgICAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1jb250aW51ZVxuICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgICAgfVxuICAgICAgICAgIGludHJpbnNpY3NbbmFtZVByb3RvdHlwZV0gPSBpbnRyaW5zaWNQcm90b3R5cGU7XG4gICAgICAgIH1cbiAgICAgIH0sXG4gICAgICBmaW5hbEludHJpbnNpY3MoKSB7XG4gICAgICAgIGZyZWV6ZShpbnRyaW5zaWNzKTtcbiAgICAgICAgcHNldWRvTmF0aXZlcyA9IG5ldyBXZWFrU2V0KFxuICAgICAgICAgIHZhbHVlcyhpbnRyaW5zaWNzKS5maWx0ZXIob2JqID0+IHR5cGVvZiBvYmogPT09ICdmdW5jdGlvbicpLFxuICAgICAgICApO1xuICAgICAgICByZXR1cm4gaW50cmluc2ljcztcbiAgICAgIH0sXG4gICAgICBpc1BzZXVkb05hdGl2ZShvYmopIHtcbiAgICAgICAgaWYgKCFwc2V1ZG9OYXRpdmVzKSB7XG4gICAgICAgICAgdGhyb3cgbmV3IEVycm9yKFxuICAgICAgICAgICAgJ2lzUHNldWRvTmF0aXZlIGNhbiBvbmx5IGJlIGNhbGxlZCBhZnRlciBmaW5hbEludHJpbnNpY3MnLFxuICAgICAgICAgICk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHBzZXVkb05hdGl2ZXMuaGFzKG9iaik7XG4gICAgICB9LFxuICAgIH07XG5cbiAgICBpbnRyaW5zaWNzQ29sbGVjdG9yLmFkZEludHJpbnNpY3MoY29uc3RhbnRQcm9wZXJ0aWVzKTtcbiAgICBpbnRyaW5zaWNzQ29sbGVjdG9yLmFkZEludHJpbnNpY3MoXG4gICAgICBzYW1wbGVHbG9iYWxzKGdsb2JhbFRoaXMsIHVuaXZlcnNhbFByb3BlcnR5TmFtZXMpLFxuICAgICk7XG5cbiAgICByZXR1cm4gaW50cmluc2ljc0NvbGxlY3RvcjtcbiAgfVxuXG4gIC8qKlxuICAgKiBnZXRHbG9iYWxJbnRyaW5zaWNzKClcbiAgICogRG9lc24ndCB0YW1lLCBkZWxldGUsIG9yIG1vZGlmeSBhbnl0aGluZy4gU2FtcGxlcyBnbG9iYWxPYmplY3QgdG8gY3JlYXRlIGFuXG4gICAqIGludHJpbnNpY3MgcmVjb3JkIGNvbnRhaW5pbmcgb25seSB0aGUgd2hpdGVsaXN0ZWQgZ2xvYmFsIHZhcmlhYmxlcywgbGlzdGVkXG4gICAqIGJ5IHRoZSBpbnRyaW5zaWMgbmFtZXMgYXBwcm9wcmlhdGUgZm9yIG5ldyBnbG9iYWxzLCBpLmUuLCB0aGUgZ2xvYmFscyBvZlxuICAgKiBuZXdseSBjb25zdHJ1Y3RlZCBjb21wYXJ0bWVudHMuXG4gICAqXG4gICAqIFdBUk5JTkc6XG4gICAqIElmIHJ1biBiZWZvcmUgbG9ja2Rvd24sIHRoZSByZXR1cm5lZCBpbnRyaW5zaWNzIHJlY29yZCB3aWxsIGNhcnJ5IHRoZVxuICAgKiAqb3JpZ2luYWwqIHVuc2FmZSAoZmVyYWwsIHVudGFtZWQpIGJpbmRpbmdzIG9mIHRoZXNlIGdsb2JhbCB2YXJpYWJsZXMuXG4gICAqXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBnbG9iYWxPYmplY3RcbiAgICovXG4gIGZ1bmN0aW9uIGdldEdsb2JhbEludHJpbnNpY3MoZ2xvYmFsT2JqZWN0KSB7XG4gICAgY29uc3QgaW50cmluc2ljc0NvbGxlY3RvciA9IG1ha2VJbnRyaW5zaWNzQ29sbGVjdG9yKCk7XG5cbiAgICBpbnRyaW5zaWNzQ29sbGVjdG9yLmFkZEludHJpbnNpY3MoXG4gICAgICBzYW1wbGVHbG9iYWxzKGdsb2JhbE9iamVjdCwgc2hhcmVkR2xvYmFsUHJvcGVydHlOYW1lcyksXG4gICAgKTtcblxuICAgIHJldHVybiBpbnRyaW5zaWNzQ29sbGVjdG9yLmZpbmFsSW50cmluc2ljcygpO1xuICB9XG5cbiAgY29uc3QgSW5lcnRDb21wYXJ0bWVudCA9IGZ1bmN0aW9uIENvbXBhcnRtZW50KFxuICAgIF9lbmRvd21lbnRzID0ge30sXG4gICAgX21vZHVsZXMgPSB7fSxcbiAgICBfb3B0aW9ucyA9IHt9LFxuICApIHtcbiAgICB0aHJvdyBuZXcgVHlwZUVycm9yKCdOb3QgYXZhaWxhYmxlJyk7XG4gIH07XG5cbiAgLyoqXG4gICAqIE9iamVjdC5nZXRDb25zdHJ1Y3Rvck9mKClcbiAgICogSGVscGVyIGZ1bmN0aW9uIHRvIGltcHJvdmUgcmVhZGFiaWxpdHksIHNpbWlsYXIgdG8gT2JqZWN0LmdldFByb3RvdHlwZU9mKCkuXG4gICAqXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBvYmpcbiAgICovXG4gIGZ1bmN0aW9uIGdldENvbnN0cnVjdG9yT2Yob2JqKSB7XG4gICAgcmV0dXJuIGdldFByb3RvdHlwZU9mKG9iaikuY29uc3RydWN0b3I7XG4gIH1cblxuICAvKipcbiAgICogZ2V0QW5vbnltb3VzSW50cmluc2ljcygpXG4gICAqIEdldCB0aGUgaW50cmluc2ljcyBub3Qgb3RoZXJ3aXNlIHJlYWNoYWJsZSBieSBuYW1lZCBvd24gcHJvcGVydHlcbiAgICogdHJhdmVyc2FsIGZyb20gdGhlIGdsb2JhbCBvYmplY3QuXG4gICAqXG4gICAqIEByZXR1cm5zIHtPYmplY3R9XG4gICAqL1xuICBmdW5jdGlvbiBnZXRBbm9ueW1vdXNJbnRyaW5zaWNzKCkge1xuICAgIGNvbnN0IEluZXJ0RnVuY3Rpb24gPSBGdW5jdGlvbi5wcm90b3R5cGUuY29uc3RydWN0b3I7XG5cbiAgICBjb25zdCBTeW1ib2xJdGVyYXRvciA9ICh0eXBlb2YgU3ltYm9sICYmIFN5bWJvbC5pdGVyYXRvcikgfHwgJ0BAaXRlcmF0b3InO1xuICAgIGNvbnN0IFN5bWJvbE1hdGNoQWxsID0gKHR5cGVvZiBTeW1ib2wgJiYgU3ltYm9sLm1hdGNoQWxsKSB8fCAnQEBtYXRjaEFsbCc7XG5cbiAgICAvLyA5LjIuNC4xICVUaHJvd1R5cGVFcnJvciVcblxuICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBwcmVmZXItcmVzdC1wYXJhbXNcbiAgICBjb25zdCBUaHJvd1R5cGVFcnJvciA9IGdldE93blByb3BlcnR5RGVzY3JpcHRvcihhcmd1bWVudHMsICdjYWxsZWUnKS5nZXQ7XG5cbiAgICAvLyAyMS4xLjUuMiBUaGUgJVN0cmluZ0l0ZXJhdG9yUHJvdG90eXBlJSBPYmplY3RcblxuICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1uZXctd3JhcHBlcnNcbiAgICBjb25zdCBTdHJpbmdJdGVyYXRvck9iamVjdCA9IG5ldyBTdHJpbmcoKVtTeW1ib2xJdGVyYXRvcl0oKTtcbiAgICBjb25zdCBTdHJpbmdJdGVyYXRvclByb3RvdHlwZSA9IGdldFByb3RvdHlwZU9mKFN0cmluZ0l0ZXJhdG9yT2JqZWN0KTtcblxuICAgIC8vIDIxLjIuNy4xIFRoZSAlUmVnRXhwU3RyaW5nSXRlcmF0b3JQcm90b3R5cGUlIE9iamVjdFxuICAgIGNvbnN0IFJlZ0V4cFN0cmluZ0l0ZXJhdG9yID1cbiAgICAgIFJlZ0V4cC5wcm90b3R5cGVbU3ltYm9sTWF0Y2hBbGxdICYmIG5ldyBSZWdFeHAoKVtTeW1ib2xNYXRjaEFsbF0oKTtcbiAgICBjb25zdCBSZWdFeHBTdHJpbmdJdGVyYXRvclByb3RvdHlwZSA9XG4gICAgICBSZWdFeHBTdHJpbmdJdGVyYXRvciAmJiBnZXRQcm90b3R5cGVPZihSZWdFeHBTdHJpbmdJdGVyYXRvcik7XG5cbiAgICAvLyAyMi4xLjUuMiBUaGUgJUFycmF5SXRlcmF0b3JQcm90b3R5cGUlIE9iamVjdFxuXG4gICAgLy8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIG5vLWFycmF5LWNvbnN0cnVjdG9yXG4gICAgY29uc3QgQXJyYXlJdGVyYXRvck9iamVjdCA9IG5ldyBBcnJheSgpW1N5bWJvbEl0ZXJhdG9yXSgpO1xuICAgIGNvbnN0IEFycmF5SXRlcmF0b3JQcm90b3R5cGUgPSBnZXRQcm90b3R5cGVPZihBcnJheUl0ZXJhdG9yT2JqZWN0KTtcblxuICAgIC8vIDIyLjIuMSBUaGUgJVR5cGVkQXJyYXklIEludHJpbnNpYyBPYmplY3RcblxuICAgIGNvbnN0IFR5cGVkQXJyYXkgPSBnZXRQcm90b3R5cGVPZihGbG9hdDMyQXJyYXkpO1xuXG4gICAgLy8gMjMuMS41LjIgVGhlICVNYXBJdGVyYXRvclByb3RvdHlwZSUgT2JqZWN0XG5cbiAgICBjb25zdCBNYXBJdGVyYXRvck9iamVjdCA9IG5ldyBNYXAoKVtTeW1ib2xJdGVyYXRvcl0oKTtcbiAgICBjb25zdCBNYXBJdGVyYXRvclByb3RvdHlwZSA9IGdldFByb3RvdHlwZU9mKE1hcEl0ZXJhdG9yT2JqZWN0KTtcblxuICAgIC8vIDIzLjIuNS4yIFRoZSAlU2V0SXRlcmF0b3JQcm90b3R5cGUlIE9iamVjdFxuXG4gICAgY29uc3QgU2V0SXRlcmF0b3JPYmplY3QgPSBuZXcgU2V0KClbU3ltYm9sSXRlcmF0b3JdKCk7XG4gICAgY29uc3QgU2V0SXRlcmF0b3JQcm90b3R5cGUgPSBnZXRQcm90b3R5cGVPZihTZXRJdGVyYXRvck9iamVjdCk7XG5cbiAgICAvLyAyNS4xLjIgVGhlICVJdGVyYXRvclByb3RvdHlwZSUgT2JqZWN0XG5cbiAgICBjb25zdCBJdGVyYXRvclByb3RvdHlwZSA9IGdldFByb3RvdHlwZU9mKEFycmF5SXRlcmF0b3JQcm90b3R5cGUpO1xuXG4gICAgLy8gMjUuMi4xIFRoZSBHZW5lcmF0b3JGdW5jdGlvbiBDb25zdHJ1Y3RvclxuXG4gICAgLy8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIG5vLWVtcHR5LWZ1bmN0aW9uXG4gICAgZnVuY3Rpb24qIEdlbmVyYXRvckZ1bmN0aW9uSW5zdGFuY2UoKSB7fVxuICAgIGNvbnN0IEdlbmVyYXRvckZ1bmN0aW9uID0gZ2V0Q29uc3RydWN0b3JPZihHZW5lcmF0b3JGdW5jdGlvbkluc3RhbmNlKTtcblxuICAgIC8vIDI1LjIuMyBQcm9wZXJ0aWVzIG9mIHRoZSBHZW5lcmF0b3JGdW5jdGlvbiBQcm90b3R5cGUgT2JqZWN0XG5cbiAgICBjb25zdCBHZW5lcmF0b3IgPSBHZW5lcmF0b3JGdW5jdGlvbi5wcm90b3R5cGU7XG5cbiAgICAvLyAyNS4zLjEgVGhlIEFzeW5jR2VuZXJhdG9yRnVuY3Rpb24gQ29uc3RydWN0b3JcblxuICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1lbXB0eS1mdW5jdGlvblxuICAgIGFzeW5jIGZ1bmN0aW9uKiBBc3luY0dlbmVyYXRvckZ1bmN0aW9uSW5zdGFuY2UoKSB7fVxuICAgIGNvbnN0IEFzeW5jR2VuZXJhdG9yRnVuY3Rpb24gPSBnZXRDb25zdHJ1Y3Rvck9mKFxuICAgICAgQXN5bmNHZW5lcmF0b3JGdW5jdGlvbkluc3RhbmNlLFxuICAgICk7XG5cbiAgICAvLyAyNS4zLjIuMiBBc3luY0dlbmVyYXRvckZ1bmN0aW9uLnByb3RvdHlwZVxuICAgIGNvbnN0IEFzeW5jR2VuZXJhdG9yID0gQXN5bmNHZW5lcmF0b3JGdW5jdGlvbi5wcm90b3R5cGU7XG4gICAgLy8gMjUuNS4xIFByb3BlcnRpZXMgb2YgdGhlIEFzeW5jR2VuZXJhdG9yIFByb3RvdHlwZSBPYmplY3RcbiAgICBjb25zdCBBc3luY0dlbmVyYXRvclByb3RvdHlwZSA9IEFzeW5jR2VuZXJhdG9yLnByb3RvdHlwZTtcbiAgICBjb25zdCBBc3luY0l0ZXJhdG9yUHJvdG90eXBlID0gZ2V0UHJvdG90eXBlT2YoQXN5bmNHZW5lcmF0b3JQcm90b3R5cGUpO1xuXG4gICAgLy8gMjUuNy4xIFRoZSBBc3luY0Z1bmN0aW9uIENvbnN0cnVjdG9yXG5cbiAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tZW1wdHktZnVuY3Rpb25cbiAgICBhc3luYyBmdW5jdGlvbiBBc3luY0Z1bmN0aW9uSW5zdGFuY2UoKSB7fVxuICAgIGNvbnN0IEFzeW5jRnVuY3Rpb24gPSBnZXRDb25zdHJ1Y3Rvck9mKEFzeW5jRnVuY3Rpb25JbnN0YW5jZSk7XG5cbiAgICBjb25zdCBpbnRyaW5zaWNzID0ge1xuICAgICAgJyVJbmVydEZ1bmN0aW9uJSc6IEluZXJ0RnVuY3Rpb24sXG4gICAgICAnJUFycmF5SXRlcmF0b3JQcm90b3R5cGUlJzogQXJyYXlJdGVyYXRvclByb3RvdHlwZSxcbiAgICAgICclSW5lcnRBc3luY0Z1bmN0aW9uJSc6IEFzeW5jRnVuY3Rpb24sXG4gICAgICAnJUFzeW5jR2VuZXJhdG9yJSc6IEFzeW5jR2VuZXJhdG9yLFxuICAgICAgJyVJbmVydEFzeW5jR2VuZXJhdG9yRnVuY3Rpb24lJzogQXN5bmNHZW5lcmF0b3JGdW5jdGlvbixcbiAgICAgICclQXN5bmNHZW5lcmF0b3JQcm90b3R5cGUlJzogQXN5bmNHZW5lcmF0b3JQcm90b3R5cGUsXG4gICAgICAnJUFzeW5jSXRlcmF0b3JQcm90b3R5cGUlJzogQXN5bmNJdGVyYXRvclByb3RvdHlwZSxcbiAgICAgICclR2VuZXJhdG9yJSc6IEdlbmVyYXRvcixcbiAgICAgICclSW5lcnRHZW5lcmF0b3JGdW5jdGlvbiUnOiBHZW5lcmF0b3JGdW5jdGlvbixcbiAgICAgICclSXRlcmF0b3JQcm90b3R5cGUlJzogSXRlcmF0b3JQcm90b3R5cGUsXG4gICAgICAnJU1hcEl0ZXJhdG9yUHJvdG90eXBlJSc6IE1hcEl0ZXJhdG9yUHJvdG90eXBlLFxuICAgICAgJyVSZWdFeHBTdHJpbmdJdGVyYXRvclByb3RvdHlwZSUnOiBSZWdFeHBTdHJpbmdJdGVyYXRvclByb3RvdHlwZSxcbiAgICAgICclU2V0SXRlcmF0b3JQcm90b3R5cGUlJzogU2V0SXRlcmF0b3JQcm90b3R5cGUsXG4gICAgICAnJVN0cmluZ0l0ZXJhdG9yUHJvdG90eXBlJSc6IFN0cmluZ0l0ZXJhdG9yUHJvdG90eXBlLFxuICAgICAgJyVUaHJvd1R5cGVFcnJvciUnOiBUaHJvd1R5cGVFcnJvcixcbiAgICAgICclVHlwZWRBcnJheSUnOiBUeXBlZEFycmF5LFxuICAgICAgJyVJbmVydENvbXBhcnRtZW50JSc6IEluZXJ0Q29tcGFydG1lbnQsXG4gICAgfTtcblxuICAgIHJldHVybiBpbnRyaW5zaWNzO1xuICB9XG5cbiAgLy8gQWRhcHRlZCBmcm9tIFNFUy9DYWphIC0gQ29weXJpZ2h0IChDKSAyMDExIEdvb2dsZSBJbmMuXG4gIC8vIENvcHlyaWdodCAoQykgMjAxOCBBZ29yaWNcblxuICAvLyBMaWNlbnNlZCB1bmRlciB0aGUgQXBhY2hlIExpY2Vuc2UsIFZlcnNpb24gMi4wICh0aGUgXCJMaWNlbnNlXCIpO1xuICAvLyB5b3UgbWF5IG5vdCB1c2UgdGhpcyBmaWxlIGV4Y2VwdCBpbiBjb21wbGlhbmNlIHdpdGggdGhlIExpY2Vuc2UuXG4gIC8vIFlvdSBtYXkgb2J0YWluIGEgY29weSBvZiB0aGUgTGljZW5zZSBhdFxuICAvL1xuICAvLyBodHRwOi8vd3d3LmFwYWNoZS5vcmcvbGljZW5zZXMvTElDRU5TRS0yLjBcbiAgLy9cbiAgLy8gVW5sZXNzIHJlcXVpcmVkIGJ5IGFwcGxpY2FibGUgbGF3IG9yIGFncmVlZCB0byBpbiB3cml0aW5nLCBzb2Z0d2FyZVxuICAvLyBkaXN0cmlidXRlZCB1bmRlciB0aGUgTGljZW5zZSBpcyBkaXN0cmlidXRlZCBvbiBhbiBcIkFTIElTXCIgQkFTSVMsXG4gIC8vIFdJVEhPVVQgV0FSUkFOVElFUyBPUiBDT05ESVRJT05TIE9GIEFOWSBLSU5ELCBlaXRoZXIgZXhwcmVzcyBvciBpbXBsaWVkLlxuICAvLyBTZWUgdGhlIExpY2Vuc2UgZm9yIHRoZSBzcGVjaWZpYyBsYW5ndWFnZSBnb3Zlcm5pbmcgcGVybWlzc2lvbnMgYW5kXG4gIC8vIGxpbWl0YXRpb25zIHVuZGVyIHRoZSBMaWNlbnNlLlxuXG4gIC8vIGJhc2VkIHVwb246XG4gIC8vIGh0dHBzOi8vZ2l0aHViLmNvbS9nb29nbGUvY2FqYS9ibG9iL21hc3Rlci9zcmMvY29tL2dvb2dsZS9jYWphL3Nlcy9zdGFydFNFUy5qc1xuICAvLyBodHRwczovL2dpdGh1Yi5jb20vZ29vZ2xlL2NhamEvYmxvYi9tYXN0ZXIvc3JjL2NvbS9nb29nbGUvY2FqYS9zZXMvcmVwYWlyRVM1LmpzXG4gIC8vIHRoZW4gY29waWVkIGZyb20gcHJvcG9zYWwtZnJvemVuLXJlYWxtcyBkZWVwLWZyZWV6ZS5qc1xuICAvLyB0aGVuIGNvcGllZCBmcm9tIFNFUy9zcmMvYnVuZGxlL2RlZXBGcmVlemUuanNcblxuICAvLyBAdHMtY2hlY2tcblxuICBjb25zdCB7IGZyZWV6ZTogZnJlZXplJDEsIGdldE93blByb3BlcnR5RGVzY3JpcHRvcnM6IGdldE93blByb3BlcnR5RGVzY3JpcHRvcnMkMSwgZ2V0UHJvdG90eXBlT2Y6IGdldFByb3RvdHlwZU9mJDEgfSA9IE9iamVjdDtcbiAgY29uc3QgeyBvd25LZXlzIH0gPSBSZWZsZWN0O1xuXG4gIC8qKlxuICAgKiBAdHlwZWRlZiB7PFQ+KHJvb3Q6IFQpID0+IFR9IEhhcmRlbmVyXG4gICAqL1xuXG4gIC8qKlxuICAgKiBDcmVhdGUgYSBgaGFyZGVuYCBmdW5jdGlvbi5cbiAgICpcbiAgICogQHJldHVybnMge0hhcmRlbmVyfVxuICAgKi9cbiAgZnVuY3Rpb24gbWFrZUhhcmRlbmVyKCkge1xuICAgIGNvbnN0IGhhcmRlbmVkID0gbmV3IFdlYWtTZXQoKTtcblxuICAgIGNvbnN0IHsgaGFyZGVuIH0gPSB7XG4gICAgICAvKipcbiAgICAgICAqIEB0ZW1wbGF0ZSBUXG4gICAgICAgKiBAcGFyYW0ge1R9IHJvb3RcbiAgICAgICAqIEByZXR1cm5zIHtUfVxuICAgICAgICovXG4gICAgICBoYXJkZW4ocm9vdCkge1xuICAgICAgICBjb25zdCB0b0ZyZWV6ZSA9IG5ldyBTZXQoKTtcbiAgICAgICAgY29uc3QgcGF0aHMgPSBuZXcgV2Vha01hcCgpO1xuXG4gICAgICAgIC8vIElmIHZhbCBpcyBzb21ldGhpbmcgd2Ugc2hvdWxkIGJlIGZyZWV6aW5nIGJ1dCBhcmVuJ3QgeWV0LFxuICAgICAgICAvLyBhZGQgaXQgdG8gdG9GcmVlemUuXG4gICAgICAgIC8qKlxuICAgICAgICAgKiBAcGFyYW0ge2FueX0gdmFsXG4gICAgICAgICAqIEBwYXJhbSB7c3RyaW5nfSBbcGF0aF1cbiAgICAgICAgICovXG4gICAgICAgIGZ1bmN0aW9uIGVucXVldWUodmFsLCBwYXRoID0gdW5kZWZpbmVkKSB7XG4gICAgICAgICAgaWYgKE9iamVjdCh2YWwpICE9PSB2YWwpIHtcbiAgICAgICAgICAgIC8vIGlnbm9yZSBwcmltaXRpdmVzXG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgfVxuICAgICAgICAgIGNvbnN0IHR5cGUgPSB0eXBlb2YgdmFsO1xuICAgICAgICAgIGlmICh0eXBlICE9PSAnb2JqZWN0JyAmJiB0eXBlICE9PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgICAgICAvLyBmdXR1cmUgcHJvb2Y6IGJyZWFrIHVudGlsIHNvbWVvbmUgZmlndXJlcyBvdXQgd2hhdCBpdCBzaG91bGQgZG9cbiAgICAgICAgICAgIHRocm93IG5ldyBUeXBlRXJyb3IoYFVuZXhwZWN0ZWQgdHlwZW9mOiAke3R5cGV9YCk7XG4gICAgICAgICAgfVxuICAgICAgICAgIGlmIChoYXJkZW5lZC5oYXModmFsKSB8fCB0b0ZyZWV6ZS5oYXModmFsKSkge1xuICAgICAgICAgICAgLy8gSWdub3JlIGlmIHRoaXMgaXMgYW4gZXhpdCwgb3Igd2UndmUgYWxyZWFkeSB2aXNpdGVkIGl0XG4gICAgICAgICAgICByZXR1cm47XG4gICAgICAgICAgfVxuICAgICAgICAgIC8vIGNvbnNvbGUubG9nKGBhZGRpbmcgJHt2YWx9IHRvIHRvRnJlZXplYCwgdmFsKTtcbiAgICAgICAgICB0b0ZyZWV6ZS5hZGQodmFsKTtcbiAgICAgICAgICBwYXRocy5zZXQodmFsLCBwYXRoKTtcbiAgICAgICAgfVxuXG4gICAgICAgIC8qKlxuICAgICAgICAgKiBAcGFyYW0ge2FueX0gb2JqXG4gICAgICAgICAqL1xuICAgICAgICBmdW5jdGlvbiBmcmVlemVBbmRUcmF2ZXJzZShvYmopIHtcbiAgICAgICAgICAvLyBOb3cgZnJlZXplIHRoZSBvYmplY3QgdG8gZW5zdXJlIHJlYWN0aXZlXG4gICAgICAgICAgLy8gb2JqZWN0cyBzdWNoIGFzIHByb3hpZXMgd29uJ3QgYWRkIHByb3BlcnRpZXNcbiAgICAgICAgICAvLyBkdXJpbmcgdHJhdmVyc2FsLCBiZWZvcmUgdGhleSBnZXQgZnJvemVuLlxuXG4gICAgICAgICAgLy8gT2JqZWN0IGFyZSB2ZXJpZmllZCBiZWZvcmUgYmVpbmcgZW5xdWV1ZWQsXG4gICAgICAgICAgLy8gdGhlcmVmb3JlIHRoaXMgaXMgYSB2YWxpZCBjYW5kaWRhdGUuXG4gICAgICAgICAgLy8gVGhyb3dzIGlmIHRoaXMgZmFpbHMgKHN0cmljdCBtb2RlKS5cbiAgICAgICAgICBmcmVlemUkMShvYmopO1xuXG4gICAgICAgICAgLy8gd2UgcmVseSB1cG9uIGNlcnRhaW4gY29tbWl0bWVudHMgb2YgT2JqZWN0LmZyZWV6ZSBhbmQgcHJveGllcyBoZXJlXG5cbiAgICAgICAgICAvLyBnZXQgc3RhYmxlL2ltbXV0YWJsZSBvdXRib3VuZCBsaW5rcyBiZWZvcmUgYSBQcm94eSBoYXMgYSBjaGFuY2UgdG8gZG9cbiAgICAgICAgICAvLyBzb21ldGhpbmcgc25lYWt5LlxuICAgICAgICAgIGNvbnN0IHBhdGggPSBwYXRocy5nZXQob2JqKSB8fCAndW5rbm93bic7XG4gICAgICAgICAgY29uc3QgZGVzY3MgPSBnZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3JzJDEob2JqKTtcbiAgICAgICAgICBjb25zdCBwcm90byA9IGdldFByb3RvdHlwZU9mJDEob2JqKTtcbiAgICAgICAgICBlbnF1ZXVlKHByb3RvLCBgJHtwYXRofS5fX3Byb3RvX19gKTtcblxuICAgICAgICAgIG93bktleXMoZGVzY3MpLmZvckVhY2gobmFtZSA9PiB7XG4gICAgICAgICAgICBjb25zdCBwYXRobmFtZSA9IGAke3BhdGh9LiR7U3RyaW5nKG5hbWUpfWA7XG4gICAgICAgICAgICAvLyB0b2RvIHVuY3VycmllZCBmb3JtXG4gICAgICAgICAgICAvLyB0b2RvOiBnZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3JzIGlzIGd1YXJhbnRlZWQgdG8gcmV0dXJuIHdlbGwtZm9ybWVkXG4gICAgICAgICAgICAvLyBkZXNjcmlwdG9ycywgYnV0IHRoZXkgc3RpbGwgaW5oZXJpdCBmcm9tIE9iamVjdC5wcm90b3R5cGUuIElmXG4gICAgICAgICAgICAvLyBzb21lb25lIGhhcyBwb2lzb25lZCBPYmplY3QucHJvdG90eXBlIHRvIGFkZCAndmFsdWUnIG9yICdnZXQnXG4gICAgICAgICAgICAvLyBwcm9wZXJ0aWVzLCB0aGVuIGEgc2ltcGxlICdpZiAoXCJ2YWx1ZVwiIGluIGRlc2MpJyBvciAnZGVzYy52YWx1ZSdcbiAgICAgICAgICAgIC8vIHRlc3QgY291bGQgYmUgY29uZnVzZWQuIFdlIHVzZSBoYXNPd25Qcm9wZXJ0eSB0byBiZSBzdXJlIGFib3V0XG4gICAgICAgICAgICAvLyB3aGV0aGVyICd2YWx1ZScgaXMgcHJlc2VudCBvciBub3QsIHdoaWNoIHRlbGxzIHVzIGZvciBzdXJlIHRoYXRcbiAgICAgICAgICAgIC8vIHRoaXMgaXMgYSBkYXRhIHByb3BlcnR5LlxuICAgICAgICAgICAgLy8gVGhlICduYW1lJyBtYXkgYmUgYSBzeW1ib2wsIGFuZCBUeXBlU2NyaXB0IGRvZXNuJ3QgbGlrZSB1cyB0b1xuICAgICAgICAgICAgLy8gaW5kZXggYXJiaXRyYXJ5IHN5bWJvbHMgb24gb2JqZWN0cywgc28gd2UgcHJldGVuZCB0aGV5J3JlIGp1c3RcbiAgICAgICAgICAgIC8vIHN0cmluZ3MuXG4gICAgICAgICAgICBjb25zdCBkZXNjID0gZGVzY3NbLyoqIEB0eXBlIHtzdHJpbmd9ICovIChuYW1lKV07XG4gICAgICAgICAgICBpZiAoJ3ZhbHVlJyBpbiBkZXNjKSB7XG4gICAgICAgICAgICAgIC8vIHRvZG8gdW5jdXJyaWVkIGZvcm1cbiAgICAgICAgICAgICAgZW5xdWV1ZShkZXNjLnZhbHVlLCBgJHtwYXRobmFtZX1gKTtcbiAgICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAgIGVucXVldWUoZGVzYy5nZXQsIGAke3BhdGhuYW1lfShnZXQpYCk7XG4gICAgICAgICAgICAgIGVucXVldWUoZGVzYy5zZXQsIGAke3BhdGhuYW1lfShzZXQpYCk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgfSk7XG4gICAgICAgIH1cblxuICAgICAgICBmdW5jdGlvbiBkZXF1ZXVlKCkge1xuICAgICAgICAgIC8vIE5ldyB2YWx1ZXMgYWRkZWQgYmVmb3JlIGZvckVhY2goKSBoYXMgZmluaXNoZWQgd2lsbCBiZSB2aXNpdGVkLlxuICAgICAgICAgIHRvRnJlZXplLmZvckVhY2goZnJlZXplQW5kVHJhdmVyc2UpOyAvLyB0b2RvIGN1cnJpZWQgZm9yRWFjaFxuICAgICAgICB9XG5cbiAgICAgICAgZnVuY3Rpb24gY29tbWl0KCkge1xuICAgICAgICAgIC8vIHRvZG8gY3VycmllZCBmb3JFYWNoXG4gICAgICAgICAgLy8gd2UgY2FwdHVyZSB0aGUgcmVhbCBXZWFrU2V0LnByb3RvdHlwZS5hZGQgYWJvdmUsIGluIGNhc2Ugc29tZW9uZVxuICAgICAgICAgIC8vIGNoYW5nZXMgaXQuIFRoZSB0d28tYXJndW1lbnQgZm9ybSBvZiBmb3JFYWNoIHBhc3NlcyB0aGUgc2Vjb25kXG4gICAgICAgICAgLy8gYXJndW1lbnQgYXMgdGhlICd0aGlzJyBiaW5kaW5nLCBzbyB3ZSBhZGQgdG8gdGhlIGNvcnJlY3Qgc2V0LlxuICAgICAgICAgIHRvRnJlZXplLmZvckVhY2goaGFyZGVuZWQuYWRkLCBoYXJkZW5lZCk7XG4gICAgICAgIH1cblxuICAgICAgICBlbnF1ZXVlKHJvb3QpO1xuICAgICAgICBkZXF1ZXVlKCk7XG4gICAgICAgIC8vIGNvbnNvbGUubG9nKFwidG9GcmVlemUgc2V0OlwiLCB0b0ZyZWV6ZSk7XG4gICAgICAgIGNvbW1pdCgpO1xuXG4gICAgICAgIHJldHVybiByb290O1xuICAgICAgfSxcbiAgICB9O1xuXG4gICAgcmV0dXJuIGhhcmRlbjtcbiAgfVxuXG4gIC8vIENvcHlyaWdodCAoQykgMjAxMSBHb29nbGUgSW5jLlxuXG4gIGNvbnN0IHsgYXBwbHk6IGFwcGx5JDEsIG93bktleXM6IG93bktleXMkMSB9ID0gUmVmbGVjdDtcbiAgY29uc3QgdW5jdXJyeVRoaXMkMSA9IGZuID0+ICh0aGlzQXJnLCAuLi5hcmdzKSA9PiBhcHBseSQxKGZuLCB0aGlzQXJnLCBhcmdzKTtcbiAgY29uc3QgaGFzT3duUHJvcGVydHkgPSB1bmN1cnJ5VGhpcyQxKE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkpO1xuXG4gIC8qKlxuICAgKiBhc1N0cmluZ1Byb3BlcnR5TmFtZSgpXG4gICAqXG4gICAqIEBwYXJhbSB7c3RyaW5nfSBwYXRoXG4gICAqIEBwYXJhbSB7c3RyaW5nIHwgc3ltYm9sfSBwcm9wXG4gICAqL1xuICBmdW5jdGlvbiBhc1N0cmluZ1Byb3BlcnR5TmFtZShwYXRoLCBwcm9wKSB7XG4gICAgaWYgKHR5cGVvZiBwcm9wID09PSAnc3RyaW5nJykge1xuICAgICAgcmV0dXJuIHByb3A7XG4gICAgfVxuXG4gICAgaWYgKHR5cGVvZiBwcm9wID09PSAnc3ltYm9sJykge1xuICAgICAgcmV0dXJuIGBAQCR7cHJvcC50b1N0cmluZygpLnNsaWNlKDE0LCAtMSl9YDtcbiAgICB9XG5cbiAgICB0aHJvdyBuZXcgVHlwZUVycm9yKGBVbmV4cGVjdGVkIHByb3BlcnR5IG5hbWUgdHlwZSAke3BhdGh9ICR7cHJvcH1gKTtcbiAgfVxuXG4gIC8qKlxuICAgKiB3aGl0ZWxpc3RJbnRyaW5zaWNzKClcbiAgICogUmVtb3ZlcyBhbGwgbm9uLXdoaXRlbGlzdGVkIHByb3BlcnRpZXMgZm91bmQgYnkgcmVjdXJzaXZlbHkgYW5kXG4gICAqIHJlZmxlY3RpdmVseSB3YWxraW5nIG93biBwcm9wZXJ0eSBjaGFpbnMuXG4gICAqXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBpbnRyaW5zaWNzXG4gICAqIEBwYXJhbSB7KE9iamVjdCkgPT4gdm9pZH0gbmF0aXZlQnJhbmRlclxuICAgKi9cbiAgZnVuY3Rpb24gd2hpdGVsaXN0SW50cmluc2ljcyhpbnRyaW5zaWNzLCBuYXRpdmVCcmFuZGVyKSB7XG4gICAgLy8gVGhlc2UgcHJpbWl0aWVzIGFyZSBhbGxvd2VkIGFsbG93ZWQgZm9yIHBlcm1pdHMuXG4gICAgY29uc3QgcHJpbWl0aXZlcyA9IFsndW5kZWZpbmVkJywgJ2Jvb2xlYW4nLCAnbnVtYmVyJywgJ3N0cmluZycsICdzeW1ib2wnXTtcblxuICAgIC8qXG4gICAgICogd2hpdGVsaXN0UHJvdG90eXBlKClcbiAgICAgKiBWYWxpZGF0ZSB0aGUgb2JqZWN0J3MgW1twcm90b3R5cGVdXSBhZ2FpbnN0IGEgcGVybWl0LlxuICAgICAqL1xuICAgIGZ1bmN0aW9uIHdoaXRlbGlzdFByb3RvdHlwZShwYXRoLCBvYmosIHByb3RvTmFtZSkge1xuICAgICAgaWYgKG9iaiAhPT0gT2JqZWN0KG9iaikpIHtcbiAgICAgICAgdGhyb3cgbmV3IFR5cGVFcnJvcihgT2JqZWN0IGV4cGVjdGVkOiAke3BhdGh9LCAke29ian0sICR7cHJvdG9OYW1lfWApO1xuICAgICAgfVxuICAgICAgY29uc3QgcHJvdG8gPSBnZXRQcm90b3R5cGVPZihvYmopO1xuXG4gICAgICAvLyBOdWxsIHByb3RvdHlwZS5cbiAgICAgIGlmIChwcm90byA9PT0gbnVsbCAmJiBwcm90b05hbWUgPT09IG51bGwpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgICAgfVxuXG4gICAgICAvLyBBc3NlcnQ6IHByb3RvTmFtZSwgaWYgcHJvdmlkZWQsIGlzIGEgc3RyaW5nLlxuICAgICAgaWYgKHByb3RvTmFtZSAhPT0gdW5kZWZpbmVkICYmIHR5cGVvZiBwcm90b05hbWUgIT09ICdzdHJpbmcnKSB7XG4gICAgICAgIHRocm93IG5ldyBUeXBlRXJyb3IoYE1hbGZvcm1lZCB3aGl0ZWxpc3QgcGVybWl0ICR7cGF0aH0uX19wcm90b19fYCk7XG4gICAgICB9XG5cbiAgICAgIC8vIElmIHBlcm1pdCBub3Qgc3BlY2lmaWVkLCBkZWZhdWx0IHRvIE9iamVjdC5wcm90b3R5cGUuXG4gICAgICBpZiAocHJvdG8gPT09IGludHJpbnNpY3NbcHJvdG9OYW1lIHx8ICclT2JqZWN0UHJvdG90eXBlJSddKSB7XG4gICAgICAgIHJldHVybjtcbiAgICAgIH1cblxuICAgICAgLy8gV2UgY2FuJ3QgY2xlYW4gW1twcm90b3R5cGVdXSwgdGhlcmVmb3JlIGFib3J0LlxuICAgICAgdGhyb3cgbmV3IEVycm9yKGBVbmV4cGVjdGVkIGludHJpbnNpYyAke3BhdGh9Ll9fcHJvdG9fXyBhdCAke3Byb3RvTmFtZX1gKTtcbiAgICB9XG5cbiAgICAvKlxuICAgICAqIGlzV2hpdGVsaXN0UHJvcGVydHlWYWx1ZSgpXG4gICAgICogV2hpdGVsaXN0IGEgc2luZ2xlIHByb3BlcnR5IHZhbHVlIGFnYWluc3QgYSBwZXJtaXQuXG4gICAgICovXG4gICAgZnVuY3Rpb24gaXNXaGl0ZWxpc3RQcm9wZXJ0eVZhbHVlKHBhdGgsIHZhbHVlLCBwcm9wLCBwZXJtaXQpIHtcbiAgICAgIGlmICh0eXBlb2YgcGVybWl0ID09PSAnb2JqZWN0Jykge1xuICAgICAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tdXNlLWJlZm9yZS1kZWZpbmVcbiAgICAgICAgd2hpdGVsaXN0UHJvcGVydGllcyhwYXRoLCB2YWx1ZSwgcGVybWl0KTtcbiAgICAgICAgLy8gVGhlIHByb3BlcnR5IGlzIHdoaXRlbGlzdGVkLlxuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgIH1cblxuICAgICAgaWYgKHBlcm1pdCA9PT0gZmFsc2UpIHtcbiAgICAgICAgLy8gQSBib29sYW4gJ2ZhbHNlJyBwZXJtaXQgc3BlY2lmaWVzIHRoZSByZW1vdmFsIG9mIGEgcHJvcGVydHkuXG4gICAgICAgIC8vIFdlIHJlcXVpcmUgYSBtb3JlIHNwZWNpZmljIHBlcm1pdCBpbnN0ZWFkIG9mIGFsbG93aW5nICd0cnVlJy5cbiAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgfVxuXG4gICAgICBpZiAodHlwZW9mIHBlcm1pdCA9PT0gJ3N0cmluZycpIHtcbiAgICAgICAgLy8gQSBzdHJpbmcgcGVybWl0IGNhbiBoYXZlIG9uZSBvZiB0d28gbWVhbmluZ3M6XG5cbiAgICAgICAgaWYgKHByb3AgPT09ICdwcm90b3R5cGUnIHx8IHByb3AgPT09ICdjb25zdHJ1Y3RvcicpIHtcbiAgICAgICAgICAvLyBGb3IgcHJvdG90eXBlIGFuZCBjb25zdHJ1Y3RvciB2YWx1ZSBwcm9wZXJ0aWVzLCB0aGUgcGVybWl0XG4gICAgICAgICAgLy8gaXMgdGhlIG5hbWUgb2YgYW4gaW50cmluc2ljLlxuICAgICAgICAgIC8vIEFzc3VtcHRpb246IHByb3RvdHlwZSBhbmQgY29uc3RydWN0b3IgY2Fubm90IGJlIHByaW1pdGl2ZXMuXG4gICAgICAgICAgLy8gQXNzZXJ0OiB0aGUgcGVybWl0IGlzIHRoZSBuYW1lIG9mIGFuIGludHJpbnNpYy5cbiAgICAgICAgICAvLyBBc3NlcnQ6IHRoZSBwcm9wZXJ0eSB2YWx1ZSBpcyBlcXVhbCB0byB0aGF0IGludHJpbnNpYy5cblxuICAgICAgICAgIGlmIChoYXNPd25Qcm9wZXJ0eShpbnRyaW5zaWNzLCBwZXJtaXQpKSB7XG4gICAgICAgICAgICBpZiAodmFsdWUgIT09IGludHJpbnNpY3NbcGVybWl0XSkge1xuICAgICAgICAgICAgICB0aHJvdyBuZXcgVHlwZUVycm9yKGBEb2VzIG5vdCBtYXRjaCB3aGl0ZWxpc3QgJHtwYXRofWApO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgcmV0dXJuIHRydWU7XG4gICAgICAgICAgfVxuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIC8vIEZvciBhbGwgb3RoZXIgcHJvcGVydGllcywgdGhlIHBlcm1pdCBpcyB0aGUgbmFtZSBvZiBhIHByaW1pdGl2ZS5cbiAgICAgICAgICAvLyBBc3NlcnQ6IHRoZSBwZXJtaXQgaXMgdGhlIG5hbWUgb2YgYSBwcmltaXRpdmUuXG4gICAgICAgICAgLy8gQXNzZXJ0OiB0aGUgcHJvcGVydHkgdmFsdWUgdHlwZSBpcyBlcXVhbCB0byB0aGF0IHByaW1pdGl2ZS5cblxuICAgICAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1sb25lbHktaWZcbiAgICAgICAgICBpZiAocHJpbWl0aXZlcy5pbmNsdWRlcyhwZXJtaXQpKSB7XG4gICAgICAgICAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgdmFsaWQtdHlwZW9mXG4gICAgICAgICAgICBpZiAodHlwZW9mIHZhbHVlICE9PSBwZXJtaXQpIHtcbiAgICAgICAgICAgICAgdGhyb3cgbmV3IFR5cGVFcnJvcihcbiAgICAgICAgICAgICAgICBgQXQgJHtwYXRofSBleHBlY3RlZCAke3Blcm1pdH0gbm90ICR7dHlwZW9mIHZhbHVlfWAsXG4gICAgICAgICAgICAgICk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgICB9XG4gICAgICAgIH1cbiAgICAgIH1cblxuICAgICAgdGhyb3cgbmV3IFR5cGVFcnJvcihgVW5leHBlY3RlZCB3aGl0ZWxpc3QgcGVybWl0ICR7cGVybWl0fSBhdCAke3BhdGh9YCk7XG4gICAgfVxuXG4gICAgLypcbiAgICAgKiBpc1doaXRlbGlzdFByb3BlcnR5KClcbiAgICAgKiBXaGl0ZWxpc3QgYSBzaW5nbGUgcHJvcGVydHkgYWdhaW5zdCBhIHBlcm1pdC5cbiAgICAgKi9cbiAgICBmdW5jdGlvbiBpc1doaXRlbGlzdFByb3BlcnR5KHBhdGgsIG9iaiwgcHJvcCwgcGVybWl0KSB7XG4gICAgICBjb25zdCBkZXNjID0gZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKG9iaiwgcHJvcCk7XG5cbiAgICAgIC8vIElzIHRoaXMgYSB2YWx1ZSBwcm9wZXJ0eT9cbiAgICAgIGlmIChoYXNPd25Qcm9wZXJ0eShkZXNjLCAndmFsdWUnKSkge1xuICAgICAgICBpZiAoaXNBY2Nlc3NvclBlcm1pdChwZXJtaXQpKSB7XG4gICAgICAgICAgdGhyb3cgbmV3IFR5cGVFcnJvcihgQWNjZXNzb3IgZXhwZWN0ZWQgYXQgJHtwYXRofWApO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBpc1doaXRlbGlzdFByb3BlcnR5VmFsdWUocGF0aCwgZGVzYy52YWx1ZSwgcHJvcCwgcGVybWl0KTtcbiAgICAgIH1cbiAgICAgIGlmICghaXNBY2Nlc3NvclBlcm1pdChwZXJtaXQpKSB7XG4gICAgICAgIHRocm93IG5ldyBUeXBlRXJyb3IoYEFjY2Vzc29yIG5vdCBleHBlY3RlZCBhdCAke3BhdGh9YCk7XG4gICAgICB9XG4gICAgICByZXR1cm4gKFxuICAgICAgICBpc1doaXRlbGlzdFByb3BlcnR5VmFsdWUoYCR7cGF0aH08Z2V0PmAsIGRlc2MuZ2V0LCBwcm9wLCBwZXJtaXQuZ2V0KSAmJlxuICAgICAgICBpc1doaXRlbGlzdFByb3BlcnR5VmFsdWUoYCR7cGF0aH08c2V0PmAsIGRlc2Muc2V0LCBwcm9wLCBwZXJtaXQuc2V0KVxuICAgICAgKTtcbiAgICB9XG5cbiAgICAvKlxuICAgICAqIGdldFN1YlBlcm1pdCgpXG4gICAgICovXG4gICAgZnVuY3Rpb24gZ2V0U3ViUGVybWl0KG9iaiwgcGVybWl0LCBwcm9wKSB7XG4gICAgICBjb25zdCBwZXJtaXRQcm9wID0gcHJvcCA9PT0gJ19fcHJvdG9fXycgPyAnLS1wcm90by0tJyA6IHByb3A7XG4gICAgICBpZiAoaGFzT3duUHJvcGVydHkocGVybWl0LCBwZXJtaXRQcm9wKSkge1xuICAgICAgICByZXR1cm4gcGVybWl0W3Blcm1pdFByb3BdO1xuICAgICAgfVxuXG4gICAgICBpZiAodHlwZW9mIG9iaiA9PT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICBuYXRpdmVCcmFuZGVyKG9iaik7XG4gICAgICAgIGlmIChoYXNPd25Qcm9wZXJ0eShGdW5jdGlvbkluc3RhbmNlLCBwZXJtaXRQcm9wKSkge1xuICAgICAgICAgIHJldHVybiBGdW5jdGlvbkluc3RhbmNlW3Blcm1pdFByb3BdO1xuICAgICAgICB9XG4gICAgICB9XG5cbiAgICAgIHJldHVybiB1bmRlZmluZWQ7XG4gICAgfVxuXG4gICAgLypcbiAgICAgKiB3aGl0ZWxpc3RQcm9wZXJ0aWVzKClcbiAgICAgKiBXaGl0ZWxpc3QgYWxsIHByb3BlcnRpZXMgYWdhaW5zdCBhIHBlcm1pdC5cbiAgICAgKi9cbiAgICBmdW5jdGlvbiB3aGl0ZWxpc3RQcm9wZXJ0aWVzKHBhdGgsIG9iaiwgcGVybWl0KSB7XG4gICAgICBpZiAob2JqID09PSB1bmRlZmluZWQpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgICAgfVxuXG4gICAgICBjb25zdCBwcm90b05hbWUgPSBwZXJtaXRbJ1tbUHJvdG9dXSddO1xuICAgICAgd2hpdGVsaXN0UHJvdG90eXBlKHBhdGgsIG9iaiwgcHJvdG9OYW1lKTtcblxuICAgICAgZm9yIChjb25zdCBwcm9wIG9mIG93bktleXMkMShvYmopKSB7XG4gICAgICAgIGNvbnN0IHByb3BTdHJpbmcgPSBhc1N0cmluZ1Byb3BlcnR5TmFtZShwYXRoLCBwcm9wKTtcbiAgICAgICAgY29uc3Qgc3ViUGF0aCA9IGAke3BhdGh9LiR7cHJvcFN0cmluZ31gO1xuICAgICAgICBjb25zdCBzdWJQZXJtaXQgPSBnZXRTdWJQZXJtaXQob2JqLCBwZXJtaXQsIHByb3BTdHJpbmcpO1xuXG4gICAgICAgIGlmIChzdWJQZXJtaXQpIHtcbiAgICAgICAgICAvLyBQcm9wZXJ0eSBoYXMgYSBwZXJtaXQuXG4gICAgICAgICAgaWYgKGlzV2hpdGVsaXN0UHJvcGVydHkoc3ViUGF0aCwgb2JqLCBwcm9wLCBzdWJQZXJtaXQpKSB7XG4gICAgICAgICAgICAvLyBQcm9wZXJ0eSBpcyB3aGl0ZWxpc3RlZC5cbiAgICAgICAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1jb250aW51ZVxuICAgICAgICAgICAgY29udGludWU7XG4gICAgICAgICAgfVxuICAgICAgICB9XG5cbiAgICAgICAgaWYgKHN1YlBlcm1pdCAhPT0gZmFsc2UpIHtcbiAgICAgICAgICAvLyBUaGlzIGNhbGwgdG8gYGNvbnNvbGUubG9nYCBpcyBpbnRlbnNpb25hbC4gSXQgaXMgbm90IGEgdmVzdGlnZVxuICAgICAgICAgIC8vIG9mIGEgZGVidWdnaW5nIGF0dGVtcHQuIFNlZSB0aGUgY29tbWVudCBhdCB0b3Agb2YgZmlsZSBmb3IgYW5cbiAgICAgICAgICAvLyBleHBsYW5hdGlvbi5cbiAgICAgICAgICBjb25zb2xlLmxvZyhgUmVtb3ZpbmcgJHtzdWJQYXRofWApO1xuICAgICAgICB9XG4gICAgICAgIHRyeSB7XG4gICAgICAgICAgZGVsZXRlIG9ialtwcm9wXTtcbiAgICAgICAgfSBjYXRjaCAoZXJyKSB7XG4gICAgICAgICAgaWYgKHByb3AgaW4gb2JqKSB7XG4gICAgICAgICAgICBjb25zb2xlLmVycm9yKGBmYWlsZWQgdG8gZGVsZXRlICR7c3ViUGF0aH1gLCBlcnIpO1xuICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICBjb25zb2xlLmVycm9yKGBkZWxldGluZyAke3N1YlBhdGh9IHRocmV3YCwgZXJyKTtcbiAgICAgICAgICB9XG4gICAgICAgICAgdGhyb3cgZXJyO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgfVxuXG4gICAgLy8gU3RhcnQgcGF0aCB3aXRoICdpbnRyaW5zaWNzJyB0byBjbGFyaWZ5IHRoYXQgcHJvcGVydGllcyBhcmUgbm90XG4gICAgLy8gcmVtb3ZlZCBmcm9tIHRoZSBnbG9iYWwgb2JqZWN0IGJ5IHRoZSB3aGl0ZWxpc3Rpbmcgb3BlcmF0aW9uLlxuICAgIHdoaXRlbGlzdFByb3BlcnRpZXMoJ2ludHJpbnNpY3MnLCBpbnRyaW5zaWNzLCB3aGl0ZWxpc3QpO1xuICB9XG5cbiAgLy8gQWRhcHRlZCBmcm9tIFNFUy9DYWphIC0gQ29weXJpZ2h0IChDKSAyMDExIEdvb2dsZSBJbmMuXG5cbiAgLyoqXG4gICAqIFJlcGxhY2UgdGhlIGxlZ2FjeSBhY2Nlc3NvcnMgb2YgT2JqZWN0IHRvIGNvbXBseSB3aXRoIHN0cmljdCBtb2RlXG4gICAqIGFuZCBFUzIwMTYgc2VtYW50aWNzLCB3ZSBkbyB0aGlzIGJ5IHJlZGVmaW5pbmcgdGhlbSB3aGlsZSBpbiAndXNlIHN0cmljdCcuXG4gICAqXG4gICAqIHRvZG86IGxpc3QgdGhlIGlzc3VlcyByZXNvbHZlZFxuICAgKlxuICAgKiBUaGlzIGZ1bmN0aW9uIGNhbiBiZSB1c2VkIGluIHR3byB3YXlzOiAoMSkgaW52b2tlZCBkaXJlY3RseSB0byBmaXggdGhlIHByaW1hbFxuICAgKiByZWFsbSdzIE9iamVjdC5wcm90b3R5cGUsIGFuZCAoMikgY29udmVydGVkIHRvIGEgc3RyaW5nIHRvIGJlIGV4ZWN1dGVkXG4gICAqIGluc2lkZSBlYWNoIG5ldyBSb290UmVhbG0gdG8gZml4IHRoZWlyIE9iamVjdC5wcm90b3R5cGVzLiBFdmFsdWF0aW9uIHJlcXVpcmVzXG4gICAqIHRoZSBmdW5jdGlvbiB0byBoYXZlIG5vIGRlcGVuZGVuY2llcywgc28gZG9uJ3QgaW1wb3J0IGFueXRoaW5nIGZyb21cbiAgICogdGhlIG91dHNpZGUuXG4gICAqL1xuXG4gIGZ1bmN0aW9uIHJlcGFpckxlZ2FjeUFjY2Vzc29ycygpIHtcbiAgICB0cnkge1xuICAgICAgLy8gVmVyaWZ5IHRoYXQgdGhlIG1ldGhvZCBpcyBub3QgY2FsbGFibGUuXG4gICAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tdW5kZXJzY29yZS1kYW5nbGVcbiAgICAgICgwLCBPYmplY3QucHJvdG90eXBlLl9fbG9va3VwR2V0dGVyX18pKCd4Jyk7XG4gICAgfSBjYXRjaCAoaWdub3JlKSB7XG4gICAgICAvLyBUaHJvd3MsIG5vIG5lZWQgdG8gcGF0Y2guXG4gICAgICByZXR1cm47XG4gICAgfVxuXG4gICAgLy8gT24gc29tZSBwbGF0Zm9ybXMsIHRoZSBpbXBsZW1lbnRhdGlvbiBvZiB0aGVzZSBmdW5jdGlvbnMgYWN0IGFzXG4gICAgLy8gaWYgdGhleSBhcmUgaW4gc2xvcHB5IG1vZGU6IGlmIHRoZXkncmUgaW52b2tlZCBiYWRseSwgdGhleSB3aWxsXG4gICAgLy8gZXhwb3NlIHRoZSBnbG9iYWwgb2JqZWN0LCBzbyB3ZSBuZWVkIHRvIHJlcGFpciB0aGVzZSBmb3JcbiAgICAvLyBzZWN1cml0eS4gVGh1cyBpdCBpcyBvdXIgcmVzcG9uc2liaWxpdHkgdG8gZml4IHRoaXMsIGFuZCB3ZSBuZWVkXG4gICAgLy8gdG8gaW5jbHVkZSByZXBhaXJBY2Nlc3NvcnMuIEUuZy4gQ2hyb21lIGluIDIwMTYuXG5cbiAgICBmdW5jdGlvbiB0b09iamVjdChvYmopIHtcbiAgICAgIGlmIChvYmogPT09IHVuZGVmaW5lZCB8fCBvYmogPT09IG51bGwpIHtcbiAgICAgICAgdGhyb3cgbmV3IFR5cGVFcnJvcihcImNhbid0IGNvbnZlcnQgdW5kZWZpbmVkIG9yIG51bGwgdG8gb2JqZWN0XCIpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIE9iamVjdChvYmopO1xuICAgIH1cblxuICAgIGZ1bmN0aW9uIGFzUHJvcGVydHlOYW1lKG9iaikge1xuICAgICAgaWYgKHR5cGVvZiBvYmogPT09ICdzeW1ib2wnKSB7XG4gICAgICAgIHJldHVybiBvYmo7XG4gICAgICB9XG4gICAgICByZXR1cm4gYCR7b2JqfWA7XG4gICAgfVxuXG4gICAgZnVuY3Rpb24gYUZ1bmN0aW9uKG9iaiwgYWNjZXNzb3IpIHtcbiAgICAgIGlmICh0eXBlb2Ygb2JqICE9PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgIHRocm93IFR5cGVFcnJvcihgaW52YWxpZCAke2FjY2Vzc29yfSB1c2FnZWApO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG9iajtcbiAgICB9XG5cbiAgICBkZWZpbmVQcm9wZXJ0aWVzKG9iamVjdFByb3RvdHlwZSwge1xuICAgICAgX19kZWZpbmVHZXR0ZXJfXzoge1xuICAgICAgICB2YWx1ZTogZnVuY3Rpb24gX19kZWZpbmVHZXR0ZXJfXyhwcm9wLCBmdW5jKSB7XG4gICAgICAgICAgY29uc3QgTyA9IHRvT2JqZWN0KHRoaXMpO1xuICAgICAgICAgIGRlZmluZVByb3BlcnR5KE8sIHByb3AsIHtcbiAgICAgICAgICAgIGdldDogYUZ1bmN0aW9uKGZ1bmMsICdnZXR0ZXInKSxcbiAgICAgICAgICAgIGVudW1lcmFibGU6IHRydWUsXG4gICAgICAgICAgICBjb25maWd1cmFibGU6IHRydWUsXG4gICAgICAgICAgfSk7XG4gICAgICAgIH0sXG4gICAgICB9LFxuICAgICAgX19kZWZpbmVTZXR0ZXJfXzoge1xuICAgICAgICB2YWx1ZTogZnVuY3Rpb24gX19kZWZpbmVTZXR0ZXJfXyhwcm9wLCBmdW5jKSB7XG4gICAgICAgICAgY29uc3QgTyA9IHRvT2JqZWN0KHRoaXMpO1xuICAgICAgICAgIGRlZmluZVByb3BlcnR5KE8sIHByb3AsIHtcbiAgICAgICAgICAgIHNldDogYUZ1bmN0aW9uKGZ1bmMsICdzZXR0ZXInKSxcbiAgICAgICAgICAgIGVudW1lcmFibGU6IHRydWUsXG4gICAgICAgICAgICBjb25maWd1cmFibGU6IHRydWUsXG4gICAgICAgICAgfSk7XG4gICAgICAgIH0sXG4gICAgICB9LFxuICAgICAgX19sb29rdXBHZXR0ZXJfXzoge1xuICAgICAgICB2YWx1ZTogZnVuY3Rpb24gX19sb29rdXBHZXR0ZXJfXyhwcm9wKSB7XG4gICAgICAgICAgbGV0IE8gPSB0b09iamVjdCh0aGlzKTtcbiAgICAgICAgICBwcm9wID0gYXNQcm9wZXJ0eU5hbWUocHJvcCk7XG4gICAgICAgICAgbGV0IGRlc2M7XG4gICAgICAgICAgLy8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIG5vLWNvbmQtYXNzaWduXG4gICAgICAgICAgd2hpbGUgKE8gJiYgIShkZXNjID0gZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKE8sIHByb3ApKSkge1xuICAgICAgICAgICAgTyA9IGdldFByb3RvdHlwZU9mKE8pO1xuICAgICAgICAgIH1cbiAgICAgICAgICByZXR1cm4gZGVzYyAmJiBkZXNjLmdldDtcbiAgICAgICAgfSxcbiAgICAgIH0sXG4gICAgICBfX2xvb2t1cFNldHRlcl9fOiB7XG4gICAgICAgIHZhbHVlOiBmdW5jdGlvbiBfX2xvb2t1cFNldHRlcl9fKHByb3ApIHtcbiAgICAgICAgICBsZXQgTyA9IHRvT2JqZWN0KHRoaXMpO1xuICAgICAgICAgIHByb3AgPSBhc1Byb3BlcnR5TmFtZShwcm9wKTtcbiAgICAgICAgICBsZXQgZGVzYztcbiAgICAgICAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tY29uZC1hc3NpZ25cbiAgICAgICAgICB3aGlsZSAoTyAmJiAhKGRlc2MgPSBnZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IoTywgcHJvcCkpKSB7XG4gICAgICAgICAgICBPID0gZ2V0UHJvdG90eXBlT2YoTyk7XG4gICAgICAgICAgfVxuICAgICAgICAgIHJldHVybiBkZXNjICYmIGRlc2Muc2V0O1xuICAgICAgICB9LFxuICAgICAgfSxcbiAgICB9KTtcbiAgfVxuXG4gIC8vIFRoaXMgbW9kdWxlIHJlcGxhY2VzIHRoZSBvcmlnaW5hbCBgRnVuY3Rpb25gIGNvbnN0cnVjdG9yLCBhbmQgdGhlIG9yaWdpbmFsXG4gIC8vIGAlR2VuZXJhdG9yRnVuY3Rpb24lYCwgYCVBc3luY0Z1bmN0aW9uJWAgYW5kIGAlQXN5bmNHZW5lcmF0b3JGdW5jdGlvbiVgLFxuICAvLyB3aXRoIHNhZmUgcmVwbGFjZW1lbnRzIHRoYXQgdGhyb3cgaWYgaW52b2tlZC5cbiAgLy9cbiAgLy8gVGhlc2UgYXJlIGFsbCByZWFjaGFibGUgdmlhIHN5bnRheCwgc28gaXQgaXNuJ3Qgc3VmZmljaWVudCB0byBqdXN0XG4gIC8vIHJlcGxhY2UgZ2xvYmFsIHByb3BlcnRpZXMgd2l0aCBzYWZlIHZlcnNpb25zLiBPdXIgbWFpbiBnb2FsIGlzIHRvIHByZXZlbnRcbiAgLy8gYWNjZXNzIHRvIHRoZSBgRnVuY3Rpb25gIGNvbnN0cnVjdG9yIHRocm91Z2ggdGhlc2Ugc3RhcnRpbmcgcG9pbnRzLlxuICAvL1xuICAvLyBBZnRlciBtb2R1bGVzIGJsb2NrIGlzIGRvbmUsIHRoZSBvcmlnaW5hbHMgbXVzdCBubyBsb25nZXIgYmUgcmVhY2hhYmxlLFxuICAvLyB1bmxlc3MgYSBjb3B5IGhhcyBiZWVuIG1hZGUsIGFuZCBmdW5jdGlvbnMgY2FuIG9ubHkgYmUgY3JlYXRlZCBieSBzeW50YXhcbiAgLy8gKHVzaW5nIGV2YWwpIG9yIGJ5IGludm9raW5nIGEgcHJldmlvdXNseSBzYXZlZCByZWZlcmVuY2UgdG8gdGhlIG9yaWdpbmFscy5cbiAgLy9cbiAgLy8gVHlwaWNhbGx5LCB0aGlzIG1vZHVsZSB3aWxsIG5vdCBiZSB1c2VkIGRpcmVjdGx5LCBidXQgdmlhIHRoZVxuICAvLyBbbG9ja2Rvd24gLSBzaGltXSB3aGljaCBoYW5kbGVzIGFsbCBuZWNlc3NhcnkgcmVwYWlycyBhbmQgdGFtaW5nIGluIFNFUy5cbiAgLy9cbiAgLy8gUmVsYXRpb24gdG8gRUNNQSBzcGVjaWZpY2F0aW9uc1xuICAvL1xuICAvLyBUaGUgdGFtaW5nIG9mIGNvbnN0cnVjdG9ycyByZWFsbHkgd2FudHMgdG8gYmUgcGFydCBvZiB0aGUgc3RhbmRhcmQsIGJlY2F1c2VcbiAgLy8gbmV3IGNvbnN0cnVjdG9ycyBtYXkgYmUgYWRkZWQgaW4gdGhlIGZ1dHVyZSwgcmVhY2hhYmxlIGZyb20gc3ludGF4LCBhbmQgdGhpc1xuICAvLyBsaXN0IG11c3QgYmUgdXBkYXRlZCB0byBtYXRjaC5cbiAgLy9cbiAgLy8gSW4gYWRkaXRpb24sIHRoZSBzdGFuZGFyZCBuZWVkcyB0byBkZWZpbmUgZm91ciBuZXcgaW50cmluc2ljcyBmb3IgdGhlIHNhZmVcbiAgLy8gcmVwbGFjZW1lbnQgZnVuY3Rpb25zLiBTZWUgWy4vd2hpdGVsaXN0IGludHJpbnNpY3NdLlxuICAvL1xuICAvLyBBZGFwdGVkIGZyb20gU0VTL0NhamFcbiAgLy8gQ29weXJpZ2h0IChDKSAyMDExIEdvb2dsZSBJbmMuXG4gIC8vIGh0dHBzOi8vZ2l0aHViLmNvbS9nb29nbGUvY2FqYS9ibG9iL21hc3Rlci9zcmMvY29tL2dvb2dsZS9jYWphL3Nlcy9zdGFydFNFUy5qc1xuICAvLyBodHRwczovL2dpdGh1Yi5jb20vZ29vZ2xlL2NhamEvYmxvYi9tYXN0ZXIvc3JjL2NvbS9nb29nbGUvY2FqYS9zZXMvcmVwYWlyRVM1LmpzXG5cbiAgLyoqXG4gICAqIHRhbWVGdW5jdGlvbkNvbnN0cnVjdG9ycygpXG4gICAqIFRoaXMgYmxvY2sgcmVwbGFjZXMgdGhlIG9yaWdpbmFsIEZ1bmN0aW9uIGNvbnN0cnVjdG9yLCBhbmQgdGhlIG9yaWdpbmFsXG4gICAqICVHZW5lcmF0b3JGdW5jdGlvbiUgJUFzeW5jRnVuY3Rpb24lIGFuZCAlQXN5bmNHZW5lcmF0b3JGdW5jdGlvbiUsIHdpdGhcbiAgICogc2FmZSByZXBsYWNlbWVudHMgdGhhdCB0aHJvdyBpZiBpbnZva2VkLlxuICAgKi9cbiAgZnVuY3Rpb24gdGFtZUZ1bmN0aW9uQ29uc3RydWN0b3JzKCkge1xuICAgIHRyeSB7XG4gICAgICAvLyBWZXJpZnkgdGhhdCB0aGUgbWV0aG9kIGlzIG5vdCBjYWxsYWJsZS5cbiAgICAgICgwLCBGdW5jdGlvbi5wcm90b3R5cGUuY29uc3RydWN0b3IpKCdyZXR1cm4gMScpO1xuICAgIH0gY2F0Y2ggKGlnbm9yZSkge1xuICAgICAgLy8gVGhyb3dzLCBubyBuZWVkIHRvIHBhdGNoLlxuICAgICAgcmV0dXJuIHt9O1xuICAgIH1cblxuICAgIGNvbnN0IG5ld0ludHJpbnNpY3MgPSB7fTtcblxuICAgIC8qXG4gICAgICogVGhlIHByb2Nlc3MgdG8gcmVwYWlyIGNvbnN0cnVjdG9yczpcbiAgICAgKiAxLiBDcmVhdGUgYW4gaW5zdGFuY2Ugb2YgdGhlIGZ1bmN0aW9uIGJ5IGV2YWx1YXRpbmcgc3ludGF4XG4gICAgICogMi4gT2J0YWluIHRoZSBwcm90b3R5cGUgZnJvbSB0aGUgaW5zdGFuY2VcbiAgICAgKiAzLiBDcmVhdGUgYSBzdWJzdGl0dXRlIHRhbWVkIGNvbnN0cnVjdG9yXG4gICAgICogNC4gUmVwbGFjZSB0aGUgb3JpZ2luYWwgY29uc3RydWN0b3Igd2l0aCB0aGUgdGFtZWQgY29uc3RydWN0b3JcbiAgICAgKiA1LiBSZXBsYWNlIHRhbWVkIGNvbnN0cnVjdG9yIHByb3RvdHlwZSBwcm9wZXJ0eSB3aXRoIHRoZSBvcmlnaW5hbCBvbmVcbiAgICAgKiA2LiBSZXBsYWNlIGl0cyBbW1Byb3RvdHlwZV1dIHNsb3Qgd2l0aCB0aGUgdGFtZWQgY29uc3RydWN0b3Igb2YgRnVuY3Rpb25cbiAgICAgKi9cbiAgICBmdW5jdGlvbiByZXBhaXJGdW5jdGlvbihuYW1lLCBpbnRyaW5zaWNOYW1lLCBkZWNsYXJhdGlvbikge1xuICAgICAgbGV0IEZ1bmN0aW9uSW5zdGFuY2U7XG4gICAgICB0cnkge1xuICAgICAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tZXZhbFxuICAgICAgICBGdW5jdGlvbkluc3RhbmNlID0gKDAsIGV2YWwpKGRlY2xhcmF0aW9uKTtcbiAgICAgIH0gY2F0Y2ggKGUpIHtcbiAgICAgICAgaWYgKGUgaW5zdGFuY2VvZiBTeW50YXhFcnJvcikge1xuICAgICAgICAgIC8vIFByZXZlbnQgZmFpbHVyZSBvbiBwbGF0Zm9ybXMgd2hlcmUgYXN5bmMgYW5kL29yIGdlbmVyYXRvcnNcbiAgICAgICAgICAvLyBhcmUgbm90IHN1cHBvcnRlZC5cbiAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgLy8gUmUtdGhyb3dcbiAgICAgICAgdGhyb3cgZTtcbiAgICAgIH1cbiAgICAgIGNvbnN0IEZ1bmN0aW9uUHJvdG90eXBlID0gZ2V0UHJvdG90eXBlT2YoRnVuY3Rpb25JbnN0YW5jZSk7XG5cbiAgICAgIC8vIFByZXZlbnRzIHRoZSBldmFsdWF0aW9uIG9mIHNvdXJjZSB3aGVuIGNhbGxpbmcgY29uc3RydWN0b3Igb24gdGhlXG4gICAgICAvLyBwcm90b3R5cGUgb2YgZnVuY3Rpb25zLlxuICAgICAgLy8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIGZ1bmMtbmFtZXNcbiAgICAgIGNvbnN0IEluZXJ0Q29uc3RydWN0b3IgPSBmdW5jdGlvbigpIHtcbiAgICAgICAgdGhyb3cgbmV3IFR5cGVFcnJvcignTm90IGF2YWlsYWJsZScpO1xuICAgICAgfTtcbiAgICAgIGRlZmluZVByb3BlcnRpZXMoSW5lcnRDb25zdHJ1Y3Rvciwge1xuICAgICAgICBwcm90b3R5cGU6IHsgdmFsdWU6IEZ1bmN0aW9uUHJvdG90eXBlIH0sXG4gICAgICAgIG5hbWU6IHtcbiAgICAgICAgICB2YWx1ZTogbmFtZSxcbiAgICAgICAgICB3cml0YWJsZTogZmFsc2UsXG4gICAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlLFxuICAgICAgICB9LFxuICAgICAgfSk7XG5cbiAgICAgIGRlZmluZVByb3BlcnRpZXMoRnVuY3Rpb25Qcm90b3R5cGUsIHtcbiAgICAgICAgY29uc3RydWN0b3I6IHsgdmFsdWU6IEluZXJ0Q29uc3RydWN0b3IgfSxcbiAgICAgIH0pO1xuXG4gICAgICAvLyBSZWNvbnN0cnVjdHMgdGhlIGluaGVyaXRhbmNlIGFtb25nIHRoZSBuZXcgdGFtZWQgY29uc3RydWN0b3JzXG4gICAgICAvLyB0byBtaXJyb3IgdGhlIG9yaWdpbmFsIHNwZWNpZmllZCBpbiBub3JtYWwgSlMuXG4gICAgICBpZiAoSW5lcnRDb25zdHJ1Y3RvciAhPT0gRnVuY3Rpb24ucHJvdG90eXBlLmNvbnN0cnVjdG9yKSB7XG4gICAgICAgIHNldFByb3RvdHlwZU9mKEluZXJ0Q29uc3RydWN0b3IsIEZ1bmN0aW9uLnByb3RvdHlwZS5jb25zdHJ1Y3Rvcik7XG4gICAgICB9XG5cbiAgICAgIG5ld0ludHJpbnNpY3NbaW50cmluc2ljTmFtZV0gPSBJbmVydENvbnN0cnVjdG9yO1xuICAgIH1cblxuICAgIC8vIEhlcmUsIHRoZSBvcmRlciBvZiBvcGVyYXRpb24gaXMgaW1wb3J0YW50OiBGdW5jdGlvbiBuZWVkcyB0byBiZSByZXBhaXJlZFxuICAgIC8vIGZpcnN0IHNpbmNlIHRoZSBvdGhlciByZXBhaXJlZCBjb25zdHJ1Y3RvcnMgbmVlZCB0byBpbmhlcml0IGZyb20gdGhlXG4gICAgLy8gdGFtZWQgRnVuY3Rpb24gZnVuY3Rpb24gY29uc3RydWN0b3IuXG5cbiAgICByZXBhaXJGdW5jdGlvbignRnVuY3Rpb24nLCAnJUluZXJ0RnVuY3Rpb24lJywgJyhmdW5jdGlvbigpe30pJyk7XG4gICAgcmVwYWlyRnVuY3Rpb24oXG4gICAgICAnR2VuZXJhdG9yRnVuY3Rpb24nLFxuICAgICAgJyVJbmVydEdlbmVyYXRvckZ1bmN0aW9uJScsXG4gICAgICAnKGZ1bmN0aW9uKigpe30pJyxcbiAgICApO1xuICAgIHJlcGFpckZ1bmN0aW9uKFxuICAgICAgJ0FzeW5jRnVuY3Rpb24nLFxuICAgICAgJyVJbmVydEFzeW5jRnVuY3Rpb24lJyxcbiAgICAgICcoYXN5bmMgZnVuY3Rpb24oKXt9KScsXG4gICAgKTtcbiAgICByZXBhaXJGdW5jdGlvbihcbiAgICAgICdBc3luY0dlbmVyYXRvckZ1bmN0aW9uJyxcbiAgICAgICclSW5lcnRBc3luY0dlbmVyYXRvckZ1bmN0aW9uJScsXG4gICAgICAnKGFzeW5jIGZ1bmN0aW9uKigpe30pJyxcbiAgICApO1xuXG4gICAgcmV0dXJuIG5ld0ludHJpbnNpY3M7XG4gIH1cblxuICBmdW5jdGlvbiB0YW1lRGF0ZUNvbnN0cnVjdG9yKGRhdGVUYW1pbmcgPSAnc2FmZScpIHtcbiAgICBpZiAoZGF0ZVRhbWluZyAhPT0gJ3NhZmUnICYmIGRhdGVUYW1pbmcgIT09ICd1bnNhZmUnKSB7XG4gICAgICB0aHJvdyBuZXcgRXJyb3IoYHVucmVjb2duaXplZCBkYXRlVGFtaW5nICR7ZGF0ZVRhbWluZ31gKTtcbiAgICB9XG4gICAgY29uc3QgT3JpZ2luYWxEYXRlID0gRGF0ZTtcbiAgICBjb25zdCBEYXRlUHJvdG90eXBlID0gT3JpZ2luYWxEYXRlLnByb3RvdHlwZTtcblxuICAgIC8vIFVzZSBjb25jaXNlIG1ldGhvZHMgdG8gb2J0YWluIG5hbWVkIGZ1bmN0aW9ucyB3aXRob3V0IGNvbnN0cnVjdG9ycy5cbiAgICBjb25zdCB0YW1lZE1ldGhvZHMgPSB7XG4gICAgICBub3coKSB7XG4gICAgICAgIHJldHVybiBOYU47XG4gICAgICB9LFxuICAgIH07XG5cbiAgICAvLyBUYW1lIHRoZSBEYXRlIGNvbnN0cnVjdG9yLlxuICAgIC8vIENvbW1vbiBiZWhhdmlvclxuICAgIC8vICAgKiBuZXcgRGF0ZSh4KSBjb2VyY2VzIHggaW50byBhIG51bWJlciBhbmQgdGhlbiByZXR1cm5zIGEgRGF0ZVxuICAgIC8vICAgICBmb3IgdGhhdCBudW1iZXIgb2YgbWlsbGlzIHNpbmNlIHRoZSBlcG9jaFxuICAgIC8vICAgKiBuZXcgRGF0ZShOYU4pIHJldHVybnMgYSBEYXRlIG9iamVjdCB3aGljaCBzdHJpbmdpZmllcyB0b1xuICAgIC8vICAgICAnSW52YWxpZCBEYXRlJ1xuICAgIC8vICAgKiBuZXcgRGF0ZSh1bmRlZmluZWQpIHJldHVybnMgYSBEYXRlIG9iamVjdCB3aGljaCBzdHJpbmdpZmllcyB0b1xuICAgIC8vICAgICAnSW52YWxpZCBEYXRlJ1xuICAgIC8vIE9yaWdpbmFsRGF0ZSAobm9ybWFsIHN0YW5kYXJkKSBiZWhhdmlvclxuICAgIC8vICAgKiBEYXRlKGFueXRoaW5nKSBnaXZlcyBhIHN0cmluZyB3aXRoIHRoZSBjdXJyZW50IHRpbWVcbiAgICAvLyAgICogbmV3IERhdGUoKSByZXR1cm5zIHRoZSBjdXJyZW50IHRpbWUsIGFzIGEgRGF0ZSBvYmplY3RcbiAgICAvLyBTaGFyZWREYXRlIGJlaGF2aW9yXG4gICAgLy8gICAqIERhdGUoYW55dGhpbmcpIHJldHVybmVkICdJbnZhbGlkIERhdGUnXG4gICAgLy8gICAqIG5ldyBEYXRlKCkgcmV0dXJucyBhIERhdGUgb2JqZWN0IHdoaWNoIHN0cmluZ2lmaWVzIHRvXG4gICAgLy8gICAgICdJbnZhbGlkIERhdGUnXG4gICAgY29uc3QgbWFrZURhdGVDb25zdHJ1Y3RvciA9ICh7IHBvd2VycyA9ICdub25lJyB9ID0ge30pID0+IHtcbiAgICAgIGxldCBSZXN1bHREYXRlO1xuICAgICAgaWYgKHBvd2VycyA9PT0gJ29yaWdpbmFsJykge1xuICAgICAgICBSZXN1bHREYXRlID0gZnVuY3Rpb24gRGF0ZSguLi5yZXN0KSB7XG4gICAgICAgICAgaWYgKG5ldy50YXJnZXQgPT09IHVuZGVmaW5lZCkge1xuICAgICAgICAgICAgcmV0dXJuIFJlZmxlY3QuYXBwbHkoT3JpZ2luYWxEYXRlLCB1bmRlZmluZWQsIHJlc3QpO1xuICAgICAgICAgIH1cbiAgICAgICAgICByZXR1cm4gUmVmbGVjdC5jb25zdHJ1Y3QoT3JpZ2luYWxEYXRlLCByZXN0LCBuZXcudGFyZ2V0KTtcbiAgICAgICAgfTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIFJlc3VsdERhdGUgPSBmdW5jdGlvbiBEYXRlKC4uLnJlc3QpIHtcbiAgICAgICAgICBpZiAobmV3LnRhcmdldCA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgICAgICByZXR1cm4gJ0ludmFsaWQgRGF0ZSc7XG4gICAgICAgICAgfVxuICAgICAgICAgIGlmIChyZXN0Lmxlbmd0aCA9PT0gMCkge1xuICAgICAgICAgICAgcmVzdCA9IFtOYU5dO1xuICAgICAgICAgIH1cbiAgICAgICAgICByZXR1cm4gUmVmbGVjdC5jb25zdHJ1Y3QoT3JpZ2luYWxEYXRlLCByZXN0LCBuZXcudGFyZ2V0KTtcbiAgICAgICAgfTtcbiAgICAgIH1cblxuICAgICAgZGVmaW5lUHJvcGVydGllcyhSZXN1bHREYXRlLCB7XG4gICAgICAgIGxlbmd0aDogeyB2YWx1ZTogNyB9LFxuICAgICAgICBwcm90b3R5cGU6IHtcbiAgICAgICAgICB2YWx1ZTogRGF0ZVByb3RvdHlwZSxcbiAgICAgICAgICB3cml0YWJsZTogZmFsc2UsXG4gICAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgICAgY29uZmlndXJhYmxlOiBmYWxzZSxcbiAgICAgICAgfSxcbiAgICAgICAgcGFyc2U6IHtcbiAgICAgICAgICB2YWx1ZTogRGF0ZS5wYXJzZSxcbiAgICAgICAgICB3cml0YWJsZTogdHJ1ZSxcbiAgICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgICBjb25maWd1cmFibGU6IHRydWUsXG4gICAgICAgIH0sXG4gICAgICAgIFVUQzoge1xuICAgICAgICAgIHZhbHVlOiBEYXRlLlVUQyxcbiAgICAgICAgICB3cml0YWJsZTogdHJ1ZSxcbiAgICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgICBjb25maWd1cmFibGU6IHRydWUsXG4gICAgICAgIH0sXG4gICAgICB9KTtcbiAgICAgIHJldHVybiBSZXN1bHREYXRlO1xuICAgIH07XG4gICAgY29uc3QgSW5pdGlhbERhdGUgPSBtYWtlRGF0ZUNvbnN0cnVjdG9yKHsgcG93ZXJzOiAnb3JpZ2luYWwnIH0pO1xuICAgIGNvbnN0IFNoYXJlZERhdGUgPSBtYWtlRGF0ZUNvbnN0cnVjdG9yKHsgcG93ZXI6ICdub25lJyB9KTtcblxuICAgIGRlZmluZVByb3BlcnRpZXMoSW5pdGlhbERhdGUsIHtcbiAgICAgIG5vdzoge1xuICAgICAgICB2YWx1ZTogRGF0ZS5ub3csXG4gICAgICAgIHdyaXRhYmxlOiB0cnVlLFxuICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlLFxuICAgICAgfSxcbiAgICB9KTtcbiAgICBkZWZpbmVQcm9wZXJ0aWVzKFNoYXJlZERhdGUsIHtcbiAgICAgIG5vdzoge1xuICAgICAgICB2YWx1ZTogdGFtZWRNZXRob2RzLm5vdyxcbiAgICAgICAgd3JpdGFibGU6IHRydWUsXG4gICAgICAgIGVudW1lcmFibGU6IGZhbHNlLFxuICAgICAgICBjb25maWd1cmFibGU6IHRydWUsXG4gICAgICB9LFxuICAgIH0pO1xuXG4gICAgZGVmaW5lUHJvcGVydGllcyhEYXRlUHJvdG90eXBlLCB7XG4gICAgICBjb25zdHJ1Y3RvcjogeyB2YWx1ZTogU2hhcmVkRGF0ZSB9LFxuICAgIH0pO1xuXG4gICAgcmV0dXJuIHtcbiAgICAgICclSW5pdGlhbERhdGUlJzogSW5pdGlhbERhdGUsXG4gICAgICAnJVNoYXJlZERhdGUlJzogU2hhcmVkRGF0ZSxcbiAgICB9O1xuICB9XG5cbiAgZnVuY3Rpb24gdGFtZU1hdGhPYmplY3QobWF0aFRhbWluZyA9ICdzYWZlJykge1xuICAgIGlmIChtYXRoVGFtaW5nICE9PSAnc2FmZScgJiYgbWF0aFRhbWluZyAhPT0gJ3Vuc2FmZScpIHtcbiAgICAgIHRocm93IG5ldyBFcnJvcihgdW5yZWNvZ25pemVkIG1hdGhUYW1pbmcgJHttYXRoVGFtaW5nfWApO1xuICAgIH1cbiAgICBjb25zdCBvcmlnaW5hbE1hdGggPSBNYXRoO1xuICAgIGNvbnN0IGluaXRpYWxNYXRoID0gb3JpZ2luYWxNYXRoOyAvLyB0byBmb2xsb3cgdGhlIG5hbWluZyBwYXR0ZXJuXG5cbiAgICBjb25zdCB7IHJhbmRvbTogXywgLi4ub3RoZXJEZXNjcmlwdG9ycyB9ID0gZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9ycyhcbiAgICAgIG9yaWdpbmFsTWF0aCxcbiAgICApO1xuXG4gICAgY29uc3Qgc2hhcmVkTWF0aCA9IGNyZWF0ZShPYmplY3QucHJvdG90eXBlLCBvdGhlckRlc2NyaXB0b3JzKTtcblxuICAgIHJldHVybiB7XG4gICAgICAnJUluaXRpYWxNYXRoJSc6IGluaXRpYWxNYXRoLFxuICAgICAgJyVTaGFyZWRNYXRoJSc6IHNoYXJlZE1hdGgsXG4gICAgfTtcbiAgfVxuXG4gIGZ1bmN0aW9uIHRhbWVSZWdFeHBDb25zdHJ1Y3RvcihyZWdFeHBUYW1pbmcgPSAnc2FmZScpIHtcbiAgICBpZiAocmVnRXhwVGFtaW5nICE9PSAnc2FmZScgJiYgcmVnRXhwVGFtaW5nICE9PSAndW5zYWZlJykge1xuICAgICAgdGhyb3cgbmV3IEVycm9yKGB1bnJlY29nbml6ZWQgcmVnRXhwVGFtaW5nICR7cmVnRXhwVGFtaW5nfWApO1xuICAgIH1cbiAgICBjb25zdCBPcmlnaW5hbFJlZ0V4cCA9IFJlZ0V4cDtcbiAgICBjb25zdCBSZWdFeHBQcm90b3R5cGUgPSBPcmlnaW5hbFJlZ0V4cC5wcm90b3R5cGU7XG5cbiAgICBjb25zdCBtYWtlUmVnRXhwQ29uc3RydWN0b3IgPSAoXyA9IHt9KSA9PiB7XG4gICAgICAvLyBSZWdFeHAgaGFzIG5vbi13cml0YWJsZSBzdGF0aWMgcHJvcGVydGllcyB3ZSBuZWVkIHRvIG9taXQuXG4gICAgICBjb25zdCBSZXN1bHRSZWdFeHAgPSBmdW5jdGlvbiBSZWdFeHAoLi4ucmVzdCkge1xuICAgICAgICBpZiAobmV3LnRhcmdldCA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgICAgcmV0dXJuIE9yaWdpbmFsUmVnRXhwKC4uLnJlc3QpO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiBSZWZsZWN0LmNvbnN0cnVjdChPcmlnaW5hbFJlZ0V4cCwgcmVzdCwgbmV3LnRhcmdldCk7XG4gICAgICB9O1xuXG4gICAgICBkZWZpbmVQcm9wZXJ0aWVzKFJlc3VsdFJlZ0V4cCwge1xuICAgICAgICBsZW5ndGg6IHsgdmFsdWU6IDIgfSxcbiAgICAgICAgcHJvdG90eXBlOiB7XG4gICAgICAgICAgdmFsdWU6IFJlZ0V4cFByb3RvdHlwZSxcbiAgICAgICAgICB3cml0YWJsZTogZmFsc2UsXG4gICAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgICAgY29uZmlndXJhYmxlOiBmYWxzZSxcbiAgICAgICAgfSxcbiAgICAgICAgW1N5bWJvbC5zcGVjaWVzXTogZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKFxuICAgICAgICAgIE9yaWdpbmFsUmVnRXhwLFxuICAgICAgICAgIFN5bWJvbC5zcGVjaWVzLFxuICAgICAgICApLFxuICAgICAgfSk7XG4gICAgICByZXR1cm4gUmVzdWx0UmVnRXhwO1xuICAgIH07XG5cbiAgICBjb25zdCBJbml0aWFsUmVnRXhwID0gbWFrZVJlZ0V4cENvbnN0cnVjdG9yKCk7XG4gICAgY29uc3QgU2hhcmVkUmVnRXhwID0gbWFrZVJlZ0V4cENvbnN0cnVjdG9yKCk7XG5cbiAgICBpZiAocmVnRXhwVGFtaW5nICE9PSAndW5zYWZlJykge1xuICAgICAgZGVsZXRlIFJlZ0V4cFByb3RvdHlwZS5jb21waWxlO1xuICAgIH1cbiAgICBkZWZpbmVQcm9wZXJ0aWVzKFJlZ0V4cFByb3RvdHlwZSwge1xuICAgICAgY29uc3RydWN0b3I6IHsgdmFsdWU6IFNoYXJlZFJlZ0V4cCB9LFxuICAgIH0pO1xuXG4gICAgcmV0dXJuIHtcbiAgICAgICclSW5pdGlhbFJlZ0V4cCUnOiBJbml0aWFsUmVnRXhwLFxuICAgICAgJyVTaGFyZWRSZWdFeHAlJzogU2hhcmVkUmVnRXhwLFxuICAgIH07XG4gIH1cblxuICAvKipcbiAgICogQGZpbGUgRXhwb3J0cyB7QGNvZGUgZW5hYmxlbWVudHN9LCBhIHJlY3Vyc2l2ZWx5IGRlZmluZWRcbiAgICogSlNPTiByZWNvcmQgZGVmaW5pbmcgdGhlIG9wdGltdW0gc2V0IG9mIGludHJpbnNpY3MgcHJvcGVydGllc1xuICAgKiB0aGF0IG5lZWQgdG8gYmUgXCJyZXBhaXJlZFwiIGJlZm9yZSBoYXJkZW5pbmcgaXMgYXBwbGllZCBvblxuICAgKiBlbnZpcm9tbWVudHMgc3ViamVjdCB0byB0aGUgb3ZlcnJpZGUgbWlzdGFrZS5cbiAgICpcbiAgICogQGF1dGhvciBKRiBQYXJhZGlzXG4gICAqIEBhdXRob3IgTWFyayBTLiBNaWxsZXJcbiAgICovXG5cbiAgLyoqXG4gICAqIDxwPkJlY2F1c2UgXCJyZXBhaXJpbmdcIiByZXBsYWNlcyBkYXRhIHByb3BlcnRpZXMgd2l0aCBhY2Nlc3NvcnMsIGV2ZXJ5XG4gICAqIHRpbWUgYSByZXBhaXJlZCBwcm9wZXJ0eSBpcyBhY2Nlc3NlZCwgdGhlIGFzc29jaWF0ZWQgZ2V0dGVyIGlzIGludm9rZWQsXG4gICAqIHdoaWNoIGRlZ3JhZGVzIHRoZSBydW50aW1lIHBlcmZvcm1hbmNlIG9mIGFsbCBjb2RlIGV4ZWN1dGluZyBpbiB0aGVcbiAgICogcmVwYWlyZWQgZW52aXJvbW1lbnQsIGNvbXBhcmVkIHRvIHRoZSBub24tcmVwYWlyZWQgY2FzZS4gSW4gb3JkZXJcbiAgICogdG8gbWFpbnRhaW4gcGVyZm9ybWFuY2UsIHdlIG9ubHkgcmVwYWlyIHRoZSBwcm9wZXJ0aWVzIG9mIG9iamVjdHNcbiAgICogZm9yIHdoaWNoIGhhcmRlbmluZyBjYXVzZXMgYSBicmVha2FnZSBvZiB0aGVpciBub3JtYWwgaW50ZW5kZWQgdXNhZ2UuXG4gICAqXG4gICAqIFRoZXJlIGFyZSB0aHJlZSB1bndhbnRlZCBjYXNlczpcbiAgICogPHVsPlxuICAgKiA8bGk+T3ZlcnJpZGluZyBwcm9wZXJ0aWVzIG9uIG9iamVjdHMgdHlwaWNhbGx5IHVzZWQgYXMgcmVjb3JkcyxcbiAgICogICAgIG5hbWVseSB7QGNvZGUgXCJPYmplY3RcIn0gYW5kIHtAY29kZSBcIkFycmF5XCJ9LiBJbiB0aGUgY2FzZSBvZiBhcnJheXMsXG4gICAqICAgICB0aGUgc2l0dWF0aW9uIGlzIHVuaW50ZW50aW9uYWwsIGEgZ2l2ZW4gcHJvZ3JhbSBtaWdodCBub3QgYmUgYXdhcmVcbiAgICogICAgIHRoYXQgbm9uLW51bWVyaWNhbCBwcm9wZXJ0aWVzIGFyZSBzdG9yZWQgb24gdGhlIHVuZGVybHlpbmcgb2JqZWN0XG4gICAqICAgICBpbnN0YW5jZSwgbm90IG9uIHRoZSBhcnJheS4gV2hlbiBhbiBvYmplY3QgaXMgdHlwaWNhbGx5IHVzZWQgYXMgYVxuICAgKiAgICAgbWFwLCB3ZSByZXBhaXIgYWxsIG9mIGl0cyBwcm90b3R5cGUgcHJvcGVydGllcy5cbiAgICogPGxpPk92ZXJyaWRpbmcgcHJvcGVydGllcyBvbiBvYmplY3RzIHRoYXQgcHJvdmlkZSBkZWZhdWx0cyBvbiB0aGVpclxuICAgKiAgICAgcHJvdG90eXBlIGFuZCB0aGF0IHByb2dyYW1zIHR5cGljYWxseSBzZXQgdXNpbmcgYW4gYXNzaWdubWVudCwgc3VjaCBhc1xuICAgKiAgICAge0Bjb2RlIFwiRXJyb3IucHJvdG90eXBlLm1lc3NhZ2VcIn0gYW5kIHtAY29kZSBcIkZ1bmN0aW9uLnByb3RvdHlwZS5uYW1lXCJ9XG4gICAqICAgICAoYm90aCBkZWZhdWx0IHRvIFwiXCIpLlxuICAgKiA8bGk+U2V0dGluZy11cCBhIHByb3RvdHlwZSBjaGFpbiwgd2hlcmUgYSBjb25zdHJ1Y3RvciBpcyBzZXQgdG8gZXh0ZW5kXG4gICAqICAgICBhbm90aGVyIG9uZS4gVGhpcyBpcyB0eXBpY2FsbHkgc2V0IGJ5IGFzc2lnbm1lbnQsIGZvciBleGFtcGxlXG4gICAqICAgICB7QGNvZGUgXCJDaGlsZC5wcm90b3R5cGUuY29uc3RydWN0b3IgPSBDaGlsZFwifSwgaW5zdGVhZCBvZiBpbnZva2luZ1xuICAgKiAgICAgT2JqZWN0LmRlZmluZVByb3BlcnR5KCk7XG4gICAqXG4gICAqIDxwPkVhY2ggSlNPTiByZWNvcmQgZW51bWVyYXRlcyB0aGUgZGlzcG9zaXRpb24gb2YgdGhlIHByb3BlcnRpZXMgb25cbiAgICogc29tZSBjb3JyZXNwb25kaW5nIGludHJpbnNpYyBvYmplY3QuXG4gICAqXG4gICAqIDxwPkZvciBlYWNoIHN1Y2ggcmVjb3JkLCB0aGUgdmFsdWVzIGFzc29jaWF0ZWQgd2l0aCBpdHMgcHJvcGVydHlcbiAgICogbmFtZXMgY2FuIGJlOlxuICAgKiA8dWw+XG4gICAqIDxsaT50cnVlLCBpbiB3aGljaCBjYXNlIHRoaXMgcHJvcGVydHkgaXMgc2ltcGx5IHJlcGFpcmVkLiBUaGVcbiAgICogICAgIHZhbHVlIGFzc29jaWF0ZWQgd2l0aCB0aGF0IHByb3BlcnR5IGlzIG5vdCB0cmF2ZXJzZWQuIEZvclxuICAgKiBcdCAgIGV4YW1wbGUsIHtAY29kZSBcIkZ1bmN0aW9uLnByb3RvdHlwZS5uYW1lXCJ9IGxlYWRzIHRvIHRydWUsXG4gICAqICAgICBtZWFuaW5nIHRoYXQgdGhlIHtAY29kZSBcIm5hbWVcIn0gcHJvcGVydHkgb2Yge0Bjb2RlXG4gICAqICAgICBcIkZ1bmN0aW9uLnByb3RvdHlwZVwifSBzaG91bGQgYmUgcmVwYWlyZWQgKHdoaWNoIGlzIG5lZWRlZFxuICAgKiAgICAgd2hlbiBpbmhlcml0aW5nIGZyb20gQGNvZGV7RnVuY3Rpb259IGFuZCBzZXR0aW5nIHRoZSBzdWJjbGFzcydzXG4gICAqICAgICB7QGNvZGUgXCJwcm90b3R5cGUubmFtZVwifSBwcm9wZXJ0eSkuIElmIHRoZSBwcm9wZXJ0eSBpc1xuICAgKiAgICAgYWxyZWFkeSBhbiBhY2Nlc3NvciBwcm9wZXJ0eSwgaXQgaXMgbm90IHJlcGFpcmVkIChiZWNhdXNlXG4gICAqICAgICBhY2Nlc3NvcnMgYXJlIG5vdCBzdWJqZWN0IHRvIHRoZSBvdmVycmlkZSBtaXN0YWtlKS5cbiAgICogPGxpPlwiKlwiLCBpbiB3aGljaCBjYXNlIHRoaXMgcHJvcGVydHkgaXMgbm90IHJlcGFpcmVkIGJ1dCB0aGVcbiAgICogICAgIHZhbHVlIGFzc29jaWF0ZWQgd2l0aCB0aGF0IHByb3BlcnR5IGFyZSB0cmF2ZXJzZWQgYW5kIHJlcGFpcmVkLlxuICAgKiA8bGk+QW5vdGhlciByZWNvcmQsIGluIHdoaWNoIGNhc2UgdGhpcyBwcm9wZXJ0eSBpcyBub3QgcmVwYWlyZWRcbiAgICogICAgIGFuZCB0aGF0IG5leHQgcmVjb3JkIHJlcHJlc2VudHMgdGhlIGRpc3Bvc2l0aW9uIG9mIHRoZSBvYmplY3RcbiAgICogICAgIHdoaWNoIGlzIGl0cyB2YWx1ZS4gRm9yIGV4YW1wbGUse0Bjb2RlIFwiRnVuY3Rpb25Qcm90b3R5cGVcIn1cbiAgICogICAgIGxlYWRzIHRvIGFub3RoZXIgcmVjb3JkIGV4cGxhaW5pbmcgd2hpY2ggcHJvcGVydGllcyB7QGNvZGVcbiAgICogICAgIEZ1bmN0aW9uLnByb3RvdHlwZX0gbmVlZCB0byBiZSByZXBhaXJlZC5cbiAgICovXG4gIGNvbnN0IG1vZGVyYXRlRW5hYmxlbWVudHMgPSB7XG4gICAgJyVPYmplY3RQcm90b3R5cGUlJzoge1xuICAgICAgLy8gQWNvcm4gNyBkb2VzIG92ZXJyaWRlIGBjb25zdHJ1Y3RvcmAgYnkgYXNzaWdubWVudCwgYnV0XG4gICAgICAvLyB0aGlzIGlzIGZpeGVkIGFzIG9mIGFjb3JuIDguIEluY2x1ZGluZyB0aGUgY29tbWVudGVkIG91dFxuICAgICAgLy8gbGluZSBiZWxvdyBpbiB0aGlzIGxpc3QgY29uZnVzZXMgdGhlIE5vZGUgY29uc29sZS5cbiAgICAgIC8vIFNlZSBodHRwczovL2dpdGh1Yi5jb20vQWdvcmljL2Fnb3JpYy1zZGsvaXNzdWVzLzIzMjRcbiAgICAgIC8vXG4gICAgICAvLyBTbyBwbGVhc2UgdXBkYXRlIGFsbFxuICAgICAgLy8gYWNvcm4gZGVwZW5kZW5jaWVzIHRvIGF0IGxlYXN0IDggaW5zdGVhZC4gV2UgYXJlIHVuYWJsZSB0byBkb1xuICAgICAgLy8gc28gYXQgdGhpcyB0aW1lIGR1ZSB0byBhIGRlcGVuZGVuY3kgdmlhIHJvbGx1cC4gSW5zdGVhZCB3ZVxuICAgICAgLy8gZG8gYSBwb3N0LWluc3RhbGwgcGF0Y2ggb2YgYWNvcm4uXG4gICAgICAvLyBTZWUgaHR0cHM6Ly9naXRodWIuY29tL0Fnb3JpYy9TRVMtc2hpbS9wdWxsLzU4OFxuICAgICAgLy8gSWYgeW91IGFyZSBzaW1pbGFybHkgc3R1Y2ssIGRvIGxpa2V3aXNlLiBPciB1bmNvbW1lbnQgb3V0XG4gICAgICAvLyB0aGUgZm9sbG93aW5nIGxpbmUgYW5kIGxldCB1cyBrbm93IHdoeS4gVGhlIG9ubHkga25vd25cbiAgICAgIC8vIGNvc3QgaXMgdGhlIHVnbHkgZGlzcGxheSBmcm9tIHRoZSBOb2RlIGNvbnNvbGUuXG4gICAgICAvL1xuICAgICAgLy8gY29uc3RydWN0b3I6IHRydWUsIC8vIHNldCBieSBhY29ybiA3LCBkMy1jb2xvclxuXG4gICAgICAvLyBBcyBleHBsYWluZWQgYXRcbiAgICAgIC8vIGh0dHBzOi8vZ2l0aHViLmNvbS92ZWdhL3ZlZ2EvaXNzdWVzLzMwNzVcbiAgICAgIC8vIHZlZ2Egb3ZlcnJpZGVzIGBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5YCBieVxuICAgICAgLy8gYXNzaWdubWVudC4gVGhvc2UgcnVubmluZyBpbnRvIHRoaXMgc2hvdWxkIGNvbnNpZGVyIGFwcGx5aW5nXG4gICAgICAvLyB0aGUgcGF0Y2hcbiAgICAgIC8vIGh0dHBzOi8vZ2l0aHViLmNvbS9BZ29yaWMvYWdvcmljLXNkay9ibG9iL21hc3Rlci9wYXRjaGVzL3ZlZ2EtdXRpbCUyQjEuMTYuMC5wYXRjaFxuICAgICAgLy8gYXMgd2UgZG8sIG9yXG4gICAgICAvLyBodHRwczovL2dpdGh1Yi5jb20vdmVnYS92ZWdhL3B1bGwvMzEwOS9jb21taXRzLzUwNzQxYzdlOTAzNWM0MDcyMDVhZTQ1OTgzNDcwYjhjYjI3YzJkYTdcbiAgICAgIC8vIFRoZSBvd25lciBvZiB2ZWdhIGlzIGF3YXJlIG9mIHRoZSBjb25jZXJuLCBzbyB0aGlzXG4gICAgICAvLyBtYXkgZXZlbnR1YWxseSBiZSBmaXhlZCBhdCB0aGUgc291cmNlLlxuICAgICAgLy8gaGFzT3duUHJvcGVydHk6IHRydWUsIC8vIHNldCBieSBcInZlZ2EtdXRpbFwiLlxuXG4gICAgICB0b1N0cmluZzogdHJ1ZSxcbiAgICAgIHZhbHVlT2Y6IHRydWUsXG4gICAgfSxcblxuICAgICclQXJyYXlQcm90b3R5cGUlJzoge1xuICAgICAgdG9TdHJpbmc6IHRydWUsXG4gICAgICBwdXNoOiB0cnVlLCAvLyBzZXQgYnkgXCJHb29nbGUgQW5hbHl0aWNzXCJcbiAgICB9LFxuXG4gICAgLy8gRnVuY3Rpb24ucHJvdG90eXBlIGhhcyBubyAncHJvdG90eXBlJyBwcm9wZXJ0eSB0byBlbmFibGUuXG4gICAgLy8gRnVuY3Rpb24gaW5zdGFuY2VzIGhhdmUgdGhlaXIgb3duICduYW1lJyBhbmQgJ2xlbmd0aCcgcHJvcGVydGllc1xuICAgIC8vIHdoaWNoIGFyZSBjb25maWd1cmFibGUgYW5kIG5vbi13cml0YWJsZS4gVGh1cywgdGhleSBhcmUgYWxyZWFkeVxuICAgIC8vIG5vbi1hc3NpZ25hYmxlIGFueXdheS5cbiAgICAnJUZ1bmN0aW9uUHJvdG90eXBlJSc6IHtcbiAgICAgIGNvbnN0cnVjdG9yOiB0cnVlLCAvLyBzZXQgYnkgXCJyZWdlbmVyYXRvci1ydW50aW1lXCJcbiAgICAgIGJpbmQ6IHRydWUsIC8vIHNldCBieSBcInVuZGVyc2NvcmVcIiwgXCJleHByZXNzXCJcbiAgICAgIHRvU3RyaW5nOiB0cnVlLCAvLyBzZXQgYnkgXCJyb2xsdXBcIlxuICAgIH0sXG5cbiAgICAnJUVycm9yUHJvdG90eXBlJSc6IHtcbiAgICAgIGNvbnN0cnVjdG9yOiB0cnVlLCAvLyBzZXQgYnkgXCJmYXN0LWpzb24tcGF0Y2hcIiwgXCJub2RlLWZldGNoXCJcbiAgICAgIG1lc3NhZ2U6IHRydWUsXG4gICAgICBuYW1lOiB0cnVlLCAvLyBzZXQgYnkgXCJwcmVjb25kXCIsIFwiYXZhXCIsIFwibm9kZS1mZXRjaFwiXG4gICAgICB0b1N0cmluZzogdHJ1ZSwgLy8gc2V0IGJ5IFwiYmx1ZWJpcmRcIlxuICAgIH0sXG5cbiAgICAnJVR5cGVFcnJvclByb3RvdHlwZSUnOiB7XG4gICAgICBjb25zdHJ1Y3RvcjogdHJ1ZSwgLy8gc2V0IGJ5IFwicmVhZGFibGUtc3RyZWFtXCJcbiAgICAgIG1lc3NhZ2U6IHRydWUsIC8vIHNldCBieSBcInRhcGVcIlxuICAgICAgbmFtZTogdHJ1ZSwgLy8gc2V0IGJ5IFwicmVhZGFibGUtc3RyZWFtXCJcbiAgICB9LFxuXG4gICAgJyVTeW50YXhFcnJvclByb3RvdHlwZSUnOiB7XG4gICAgICBtZXNzYWdlOiB0cnVlLCAvLyB0byBtYXRjaCBUeXBlRXJyb3JQcm90b3R5cGUubWVzc2FnZVxuICAgIH0sXG5cbiAgICAnJVJhbmdlRXJyb3JQcm90b3R5cGUlJzoge1xuICAgICAgbWVzc2FnZTogdHJ1ZSwgLy8gdG8gbWF0Y2ggVHlwZUVycm9yUHJvdG90eXBlLm1lc3NhZ2VcbiAgICB9LFxuXG4gICAgJyVVUklFcnJvclByb3RvdHlwZSUnOiB7XG4gICAgICBtZXNzYWdlOiB0cnVlLCAvLyB0byBtYXRjaCBUeXBlRXJyb3JQcm90b3R5cGUubWVzc2FnZVxuICAgIH0sXG5cbiAgICAnJUV2YWxFcnJvclByb3RvdHlwZSUnOiB7XG4gICAgICBtZXNzYWdlOiB0cnVlLCAvLyB0byBtYXRjaCBUeXBlRXJyb3JQcm90b3R5cGUubWVzc2FnZVxuICAgIH0sXG5cbiAgICAnJVJlZmVyZW5jZUVycm9yUHJvdG90eXBlJSc6IHtcbiAgICAgIG1lc3NhZ2U6IHRydWUsIC8vIHRvIG1hdGNoIFR5cGVFcnJvclByb3RvdHlwZS5tZXNzYWdlXG4gICAgfSxcblxuICAgICclUHJvbWlzZVByb3RvdHlwZSUnOiB7XG4gICAgICBjb25zdHJ1Y3RvcjogdHJ1ZSwgLy8gc2V0IGJ5IFwiY29yZS1qc1wiXG4gICAgfSxcblxuICAgICclVHlwZWRBcnJheVByb3RvdHlwZSUnOiAnKicsIC8vIHNldCBieSBodHRwczovL2dpdGh1Yi5jb20vZmVyb3NzL2J1ZmZlclxuXG4gICAgJyVHZW5lcmF0b3IlJzoge1xuICAgICAgY29uc3RydWN0b3I6IHRydWUsXG4gICAgICBuYW1lOiB0cnVlLFxuICAgICAgdG9TdHJpbmc6IHRydWUsXG4gICAgfSxcblxuICAgICclSXRlcmF0b3JQcm90b3R5cGUlJzoge1xuICAgICAgdG9TdHJpbmc6IHRydWUsXG4gICAgfSxcbiAgfTtcblxuICBjb25zdCBtaW5FbmFibGVtZW50cyA9IHtcbiAgICAnJU9iamVjdFByb3RvdHlwZSUnOiB7XG4gICAgICB0b1N0cmluZzogdHJ1ZSxcbiAgICB9LFxuXG4gICAgJyVGdW5jdGlvblByb3RvdHlwZSUnOiB7XG4gICAgICB0b1N0cmluZzogdHJ1ZSwgLy8gc2V0IGJ5IFwicm9sbHVwXCJcbiAgICB9LFxuXG4gICAgJyVFcnJvclByb3RvdHlwZSUnOiB7XG4gICAgICBuYW1lOiB0cnVlLCAvLyBzZXQgYnkgXCJwcmVjb25kXCIsIFwiYXZhXCIsIFwibm9kZS1mZXRjaFwiXG4gICAgfSxcbiAgfTtcblxuICAvLyBBZGFwdGVkIGZyb20gU0VTL0NhamFcblxuICBjb25zdCB7IG93bktleXM6IG93bktleXMkMiB9ID0gUmVmbGVjdDtcblxuICBmdW5jdGlvbiBpc09iamVjdChvYmopIHtcbiAgICByZXR1cm4gb2JqICE9PSBudWxsICYmIHR5cGVvZiBvYmogPT09ICdvYmplY3QnO1xuICB9XG5cbiAgLyoqXG4gICAqIEZvciBhIHNwZWNpYWwgc2V0IG9mIHByb3BlcnRpZXMgZGVmaW5lZCBpbiB0aGUgYGVuYWJsZW1lbnRgIHdoaXRlbGlzdCxcbiAgICogYGVuYWJsZVByb3BlcnR5T3ZlcnJpZGVzYCBlbnN1cmVzIHRoYXQgdGhlIGVmZmVjdCBvZiBmcmVlemluZyBkb2VzIG5vdFxuICAgKiBzdXBwcmVzcyB0aGUgYWJpbGl0eSB0byBvdmVycmlkZSB0aGVzZSBwcm9wZXJ0aWVzIG9uIGRlcml2ZWQgb2JqZWN0cyBieVxuICAgKiBzaW1wbGUgYXNzaWdubWVudC5cbiAgICpcbiAgICogQmVjYXVzZSBvZiBsYWNrIG9mIHN1ZmZpY2llbnQgZm9yZXNpZ2h0IGF0IHRoZSB0aW1lLCBFUzUgdW5mb3J0dW5hdGVseVxuICAgKiBzcGVjaWZpZWQgdGhhdCBhIHNpbXBsZSBhc3NpZ25tZW50IHRvIGEgbm9uLWV4aXN0ZW50IHByb3BlcnR5IG11c3QgZmFpbCBpZlxuICAgKiBpdCB3b3VsZCBvdmVycmlkZSBhbiBub24td3JpdGFibGUgZGF0YSBwcm9wZXJ0eSBvZiB0aGUgc2FtZSBuYW1lIGluIHRoZVxuICAgKiBzaGFkb3cgb2YgdGhlIHByb3RvdHlwZSBjaGFpbi4gSW4gcmV0cm9zcGVjdCwgdGhpcyB3YXMgYSBtaXN0YWtlLCB0aGVcbiAgICogc28tY2FsbGVkIFwib3ZlcnJpZGUgbWlzdGFrZVwiLiBCdXQgaXQgaXMgbm93IHRvbyBsYXRlIGFuZCB3ZSBtdXN0IGxpdmUgd2l0aFxuICAgKiB0aGUgY29uc2VxdWVuY2VzLlxuICAgKlxuICAgKiBBcyBhIHJlc3VsdCwgc2ltcGx5IGZyZWV6aW5nIGFuIG9iamVjdCB0byBtYWtlIGl0IHRhbXBlciBwcm9vZiBoYXMgdGhlXG4gICAqIHVuZm9ydHVuYXRlIHNpZGUgZWZmZWN0IG9mIGJyZWFraW5nIHByZXZpb3VzbHkgY29ycmVjdCBjb2RlIHRoYXQgaXNcbiAgICogY29uc2lkZXJlZCB0byBoYXZlIGZvbGxvd2VkIEpTIGJlc3QgcHJhY3RpY2VzLCBpZiB0aGlzIHByZXZpb3VzIGNvZGUgdXNlZFxuICAgKiBhc3NpZ25tZW50IHRvIG92ZXJyaWRlLlxuICAgKlxuICAgKiBGb3IgdGhlIGVuYWJsZWQgcHJvcGVydGllcywgYGVuYWJsZVByb3BlcnR5T3ZlcnJpZGVzYCBlZmZlY3RpdmVseSBzaGltcyB3aGF0XG4gICAqIHRoZSBhc3NpZ25tZW50IGJlaGF2aW9yIHdvdWxkIGhhdmUgYmVlbiBpbiB0aGUgYWJzZW5jZSBvZiB0aGUgb3ZlcnJpZGVcbiAgICogbWlzdGFrZS4gSG93ZXZlciwgdGhlIHNoaW0gcHJvZHVjZXMgYW4gaW1wZXJmZWN0IGVtdWxhdGlvbi4gSXQgc2hpbXMgdGhlXG4gICAqIGJlaGF2aW9yIGJ5IHR1cm5pbmcgdGhlc2UgZGF0YSBwcm9wZXJ0aWVzIGludG8gYWNjZXNzb3IgcHJvcGVydGllcywgd2hlcmVcbiAgICogdGhlIGFjY2Vzc29yJ3MgZ2V0dGVyIGFuZCBzZXR0ZXIgcHJvdmlkZSB0aGUgZGVzaXJlZCBiZWhhdmlvci4gRm9yXG4gICAqIG5vbi1yZWZsZWN0aXZlIG9wZXJhdGlvbnMsIHRoZSBpbGx1c2lvbiBpcyBwZXJmZWN0LiBIb3dldmVyLCByZWZsZWN0aXZlXG4gICAqIG9wZXJhdGlvbnMgbGlrZSBgZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yYCBzZWUgdGhlIGRlc2NyaXB0b3Igb2YgYW4gYWNjZXNzb3JcbiAgICogcHJvcGVydHkgcmF0aGVyIHRoYW4gdGhlIGRlc2NyaXB0b3Igb2YgYSBkYXRhIHByb3BlcnR5LiBBdCB0aGUgdGltZSBvZiB0aGlzXG4gICAqIHdyaXRpbmcsIHRoaXMgaXMgdGhlIGJlc3Qgd2Uga25vdyBob3cgdG8gZG8uXG4gICAqXG4gICAqIFRvIHRoZSBnZXR0ZXIgb2YgdGhlIGFjY2Vzc29yIHdlIGFkZCBhIHByb3BlcnR5IG5hbWVkXG4gICAqIGAnb3JpZ2luYWxWYWx1ZSdgIHdob3NlIHZhbHVlIGlzLCBhcyBpdCBzYXlzLCB0aGUgdmFsdWUgdGhhdCB0aGVcbiAgICogZGF0YSBwcm9wZXJ0eSBoYWQgYmVmb3JlIGJlaW5nIGNvbnZlcnRlZCB0byBhbiBhY2Nlc3NvciBwcm9wZXJ0eS4gV2UgYWRkXG4gICAqIHRoaXMgZXh0cmEgcHJvcGVydHkgdG8gdGhlIGdldHRlciBmb3IgdHdvIHJlYXNvbjpcbiAgICpcbiAgICogVGhlIGhhcmRlbiBhbGdvcml0aG0gd2Fsa3MgdGhlIG93biBwcm9wZXJ0aWVzIHJlZmxlY3RpdmVseSwgaS5lLiwgd2l0aFxuICAgKiBgZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yYCBzZW1hbnRpY3MsIHJhdGhlciB0aGFuIGBbW0dldF1dYCBzZW1hbnRpY3MuIFdoZW5cbiAgICogaXQgc2VlcyBhbiBhY2Nlc3NvciBwcm9wZXJ0eSwgaXQgZG9lcyBub3QgaW52b2tlIHRoZSBnZXR0ZXIuIFJhdGhlciwgaXRcbiAgICogcHJvY2VlZHMgdG8gd2FsayBib3RoIHRoZSBnZXR0ZXIgYW5kIHNldHRlciBhcyBwYXJ0IG9mIGl0cyB0cmFuc2l0aXZlXG4gICAqIHRyYXZlcnNhbC4gV2l0aG91dCB0aGlzIGV4dHJhIHByb3BlcnR5LCBgZW5hYmxlUHJvcGVydHlPdmVycmlkZXNgIHdvdWxkIGhhdmVcbiAgICogaGlkZGVuIHRoZSBvcmlnaW5hbCBkYXRhIHByb3BlcnR5IHZhbHVlIGZyb20gYGhhcmRlbmAsIHdoaWNoIHdvdWxkIGJlIGJhZC5cbiAgICogSW5zdGVhZCwgYnkgZXhwb3NpbmcgdGhhdCB2YWx1ZSBpbiBhbiBvd24gZGF0YSBwcm9wZXJ0eSBvbiB0aGUgZ2V0dGVyLFxuICAgKiBgaGFyZGVuYCBmaW5kcyBhbmQgd2Fsa3MgaXQgYW55d2F5LlxuICAgKlxuICAgKiBXZSBlbmFibGUgYSBmb3JtIG9mIGNvb3BlcmF0aXZlIGVtdWxhdGlvbiwgZ2l2aW5nIHJlZmxlY3RpdmUgY29kZSBhblxuICAgKiBvcHBvcnR1bml0eSB0byBjb29wZXJhdGUgaW4gdXBob2xkaW5nIHRoZSBpbGx1c2lvbi4gV2hlbiBzdWNoIGNvb3BlcmF0aXZlXG4gICAqIHJlZmxlY3RpdmUgY29kZSBzZWVzIGFuIGFjY2Vzc29yIHByb3BlcnR5LCB3aGVyZSB0aGUgYWNjZXNzb3IncyBnZXR0ZXJcbiAgICogaGFzIGFuIGBvcmlnaW5hbFZhbHVlYCBwcm9wZXJ0eSwgaXQga25vd3MgdGhhdCB0aGUgZ2V0dGVyIGlzXG4gICAqIGFsbGVnaW5nIHRoYXQgaXQgaXMgdGhlIHJlc3VsdCBvZiB0aGUgYGVuYWJsZVByb3BlcnR5T3ZlcnJpZGVzYCBjb252ZXJzaW9uXG4gICAqIHBhdHRlcm4sIHNvIGl0IGNhbiBkZWNpZGUgdG8gY29vcGVyYXRpdmVseSBcInByZXRlbmRcIiB0aGF0IGl0IHNlZXMgYSBkYXRhXG4gICAqIHByb3BlcnR5IHdpdGggdGhhdCB2YWx1ZS5cbiAgICpcbiAgICogQHBhcmFtIHtSZWNvcmQ8c3RyaW5nLCBhbnk+fSBpbnRyaW5zaWNzXG4gICAqIEBwYXJhbSB7J21pbicgfCAnbW9kZXJhdGUnfSBvdmVycmlkZVRhbWluZ1xuICAgKi9cbiAgZnVuY3Rpb24gZW5hYmxlUHJvcGVydHlPdmVycmlkZXMoaW50cmluc2ljcywgb3ZlcnJpZGVUYW1pbmcpIHtcbiAgICBmdW5jdGlvbiBlbmFibGUocGF0aCwgb2JqLCBwcm9wLCBkZXNjKSB7XG4gICAgICBpZiAoJ3ZhbHVlJyBpbiBkZXNjICYmIGRlc2MuY29uZmlndXJhYmxlKSB7XG4gICAgICAgIGNvbnN0IHsgdmFsdWUgfSA9IGRlc2M7XG5cbiAgICAgICAgZnVuY3Rpb24gZ2V0dGVyKCkge1xuICAgICAgICAgIHJldHVybiB2YWx1ZTtcbiAgICAgICAgfVxuICAgICAgICBkZWZpbmVQcm9wZXJ0eShnZXR0ZXIsICdvcmlnaW5hbFZhbHVlJywge1xuICAgICAgICAgIHZhbHVlLFxuICAgICAgICAgIHdyaXRhYmxlOiBmYWxzZSxcbiAgICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgICBjb25maWd1cmFibGU6IGZhbHNlLFxuICAgICAgICB9KTtcblxuICAgICAgICBmdW5jdGlvbiBzZXR0ZXIobmV3VmFsdWUpIHtcbiAgICAgICAgICBpZiAob2JqID09PSB0aGlzKSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgVHlwZUVycm9yKFxuICAgICAgICAgICAgICBgQ2Fubm90IGFzc2lnbiB0byByZWFkIG9ubHkgcHJvcGVydHkgJyR7U3RyaW5nKFxuICAgICAgICAgICAgICBwcm9wLFxuICAgICAgICAgICAgKX0nIG9mICcke3BhdGh9J2AsXG4gICAgICAgICAgICApO1xuICAgICAgICAgIH1cbiAgICAgICAgICBpZiAob2JqZWN0SGFzT3duUHJvcGVydHkodGhpcywgcHJvcCkpIHtcbiAgICAgICAgICAgIHRoaXNbcHJvcF0gPSBuZXdWYWx1ZTtcbiAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgZGVmaW5lUHJvcGVydHkodGhpcywgcHJvcCwge1xuICAgICAgICAgICAgICB2YWx1ZTogbmV3VmFsdWUsXG4gICAgICAgICAgICAgIHdyaXRhYmxlOiB0cnVlLFxuICAgICAgICAgICAgICBlbnVtZXJhYmxlOiB0cnVlLFxuICAgICAgICAgICAgICBjb25maWd1cmFibGU6IHRydWUsXG4gICAgICAgICAgICB9KTtcbiAgICAgICAgICB9XG4gICAgICAgIH1cblxuICAgICAgICBkZWZpbmVQcm9wZXJ0eShvYmosIHByb3AsIHtcbiAgICAgICAgICBnZXQ6IGdldHRlcixcbiAgICAgICAgICBzZXQ6IHNldHRlcixcbiAgICAgICAgICBlbnVtZXJhYmxlOiBkZXNjLmVudW1lcmFibGUsXG4gICAgICAgICAgY29uZmlndXJhYmxlOiBkZXNjLmNvbmZpZ3VyYWJsZSxcbiAgICAgICAgfSk7XG4gICAgICB9XG4gICAgfVxuXG4gICAgZnVuY3Rpb24gZW5hYmxlUHJvcGVydHkocGF0aCwgb2JqLCBwcm9wKSB7XG4gICAgICBjb25zdCBkZXNjID0gZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKG9iaiwgcHJvcCk7XG4gICAgICBpZiAoIWRlc2MpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgICAgfVxuICAgICAgZW5hYmxlKHBhdGgsIG9iaiwgcHJvcCwgZGVzYyk7XG4gICAgfVxuXG4gICAgZnVuY3Rpb24gZW5hYmxlQWxsUHJvcGVydGllcyhwYXRoLCBvYmopIHtcbiAgICAgIGNvbnN0IGRlc2NzID0gZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9ycyhvYmopO1xuICAgICAgaWYgKCFkZXNjcykge1xuICAgICAgICByZXR1cm47XG4gICAgICB9XG4gICAgICAvLyBUeXBlU2NyaXB0IGRvZXMgbm90IGFsbG93IHN5bWJvbHMgdG8gYmUgdXNlZCBhcyBpbmRleGVzIGJlY2F1c2UgaXRcbiAgICAgIC8vIGNhbm5vdCByZWNva29uIHR5cGVzIG9mIHN5bWJvbGl6ZWQgcHJvcGVydGllcy5cbiAgICAgIC8vIEB0cy1pZ25vcmVcbiAgICAgIG93bktleXMkMihkZXNjcykuZm9yRWFjaChwcm9wID0+IGVuYWJsZShwYXRoLCBvYmosIHByb3AsIGRlc2NzW3Byb3BdKSk7XG4gICAgfVxuXG4gICAgZnVuY3Rpb24gZW5hYmxlUHJvcGVydGllcyhwYXRoLCBvYmosIHBsYW4pIHtcbiAgICAgIGZvciAoY29uc3QgcHJvcCBvZiBnZXRPd25Qcm9wZXJ0eU5hbWVzKHBsYW4pKSB7XG4gICAgICAgIGNvbnN0IGRlc2MgPSBnZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3Iob2JqLCBwcm9wKTtcbiAgICAgICAgaWYgKCFkZXNjIHx8IGRlc2MuZ2V0IHx8IGRlc2Muc2V0KSB7XG4gICAgICAgICAgLy8gTm8gbm90IGEgdmFsdWUgcHJvcGVydHksIG5vdGhpbmcgdG8gZG8uXG4gICAgICAgICAgLy8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIG5vLWNvbnRpbnVlXG4gICAgICAgICAgY29udGludWU7XG4gICAgICAgIH1cblxuICAgICAgICAvLyBQbGFuIGhhcyBubyBzeW1ib2wga2V5cyBhbmQgd2UgdXNlIGdldE93blByb3BlcnR5TmFtZXMoKVxuICAgICAgICAvLyBzbyBgcHJvcGAgY2Fubm90IG9ubHkgYmUgYSBzdHJpbmcsIG5vdCBhIHN5bWJvbC4gV2UgY29lcmNlIGl0IGluIHBsYWNlXG4gICAgICAgIC8vIHdpdGggYFN0cmluZyguLilgIGFueXdheSBqdXN0IGFzIGdvb2QgaHlnaWVuZSwgc2luY2UgdGhlc2UgcGF0aHMgYXJlIGp1c3RcbiAgICAgICAgLy8gZm9yIGRpYWdub3N0aWMgcHVycG9zZXMuXG4gICAgICAgIGNvbnN0IHN1YlBhdGggPSBgJHtwYXRofS4ke1N0cmluZyhwcm9wKX1gO1xuICAgICAgICBjb25zdCBzdWJQbGFuID0gcGxhbltwcm9wXTtcblxuICAgICAgICBpZiAoc3ViUGxhbiA9PT0gdHJ1ZSkge1xuICAgICAgICAgIGVuYWJsZVByb3BlcnR5KHN1YlBhdGgsIG9iaiwgcHJvcCk7XG4gICAgICAgIH0gZWxzZSBpZiAoc3ViUGxhbiA9PT0gJyonKSB7XG4gICAgICAgICAgZW5hYmxlQWxsUHJvcGVydGllcyhzdWJQYXRoLCBkZXNjLnZhbHVlKTtcbiAgICAgICAgfSBlbHNlIGlmIChpc09iamVjdChzdWJQbGFuKSkge1xuICAgICAgICAgIGVuYWJsZVByb3BlcnRpZXMoc3ViUGF0aCwgZGVzYy52YWx1ZSwgc3ViUGxhbik7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgdGhyb3cgbmV3IFR5cGVFcnJvcihgVW5leHBlY3RlZCBvdmVycmlkZSBlbmFibGVtZW50IHBsYW4gJHtzdWJQYXRofWApO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgfVxuXG4gICAgbGV0IHBsYW47XG4gICAgc3dpdGNoIChvdmVycmlkZVRhbWluZykge1xuICAgICAgY2FzZSAnbWluJzoge1xuICAgICAgICBwbGFuID0gbWluRW5hYmxlbWVudHM7XG4gICAgICAgIGJyZWFrO1xuICAgICAgfVxuICAgICAgY2FzZSAnbW9kZXJhdGUnOiB7XG4gICAgICAgIHBsYW4gPSBtb2RlcmF0ZUVuYWJsZW1lbnRzO1xuICAgICAgICBicmVhaztcbiAgICAgIH1cbiAgICAgIGRlZmF1bHQ6IHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKGB1bnJlY29nbml6ZWQgb3ZlcnJpZGVUYW1pbmcgJHtvdmVycmlkZVRhbWluZ31gKTtcbiAgICAgIH1cbiAgICB9XG5cbiAgICAvLyBEbyB0aGUgcmVwYWlyLlxuICAgIGVuYWJsZVByb3BlcnRpZXMoJ3Jvb3QnLCBpbnRyaW5zaWNzLCBwbGFuKTtcbiAgfVxuXG4gIC8vIEB0cy1jaGVja1xuXG4gIC8qKlxuICAgKiBQcmVwZW5kIHRoZSBjb3JyZWN0IGluZGVmaW5pdGUgYXJ0aWNsZSBvbnRvIGEgbm91biwgdHlwaWNhbGx5IGEgdHlwZW9mXG4gICAqIHJlc3VsdCwgZS5nLiwgXCJhbiBvYmplY3RcIiB2cy4gXCJhIG51bWJlclwiXG4gICAqXG4gICAqIEBwYXJhbSB7c3RyaW5nfSBzdHIgVGhlIG5vdW4gdG8gcHJlcGVuZFxuICAgKiBAcmV0dXJucyB7c3RyaW5nfSBUaGUgbm91biBwcmVwZW5kZWQgd2l0aCBhL2FuXG4gICAqL1xuICBjb25zdCBhbiA9IHN0ciA9PiB7XG4gICAgc3RyID0gYCR7c3RyfWA7XG4gICAgaWYgKHN0ci5sZW5ndGggPj0gMSAmJiAnYWVpb3VBRUlPVScuaW5jbHVkZXMoc3RyWzBdKSkge1xuICAgICAgcmV0dXJuIGBhbiAke3N0cn1gO1xuICAgIH1cbiAgICByZXR1cm4gYGEgJHtzdHJ9YDtcbiAgfTtcbiAgZnJlZXplKGFuKTtcblxuICAvKipcbiAgICogTGlrZSBgSlNPTi5zdHJpbmdpZnlgIGJ1dCBkb2VzIG5vdCBibG93IHVwIGlmIGdpdmVuIGEgY3ljbGUgb3IgYSBiaWdpbnQuXG4gICAqIFRoaXMgaXMgbm90XG4gICAqIGludGVuZGVkIHRvIGJlIGEgc2VyaWFsaXphdGlvbiB0byBzdXBwb3J0IGFueSB1c2VmdWwgdW5zZXJpYWxpemF0aW9uLFxuICAgKiBvciBhbnkgcHJvZ3JhbW1hdGljIHVzZSBvZiB0aGUgcmVzdWx0aW5nIHN0cmluZy4gVGhlIHN0cmluZyBpcyBpbnRlbmRlZFxuICAgKiAqb25seSogZm9yIHNob3dpbmcgYSBodW1hbiB1bmRlciBiZW5pZ24gY29uZGl0aW9ucywgaW4gb3JkZXIgdG8gYmVcbiAgICogaW5mb3JtYXRpdmUgZW5vdWdoIGZvciBzb21lXG4gICAqIGxvZ2dpbmcgcHVycG9zZXMuIEFzIHN1Y2gsIHRoaXMgYGJlc3RFZmZvcnRTdHJpbmdpZnlgIGhhcyBhblxuICAgKiBpbXByZWNpc2Ugc3BlY2lmaWNhdGlvbiBhbmQgbWF5IGNoYW5nZSBvdmVyIHRpbWUuXG4gICAqXG4gICAqIFRoZSBjdXJyZW50IGBiZXN0RWZmb3J0U3RyaW5naWZ5YCBwb3NzaWJseSBlbWl0cyB0b28gbWFueSBcInNlZW5cIlxuICAgKiBtYXJraW5nczogTm90IG9ubHkgZm9yIGN5Y2xlcywgYnV0IGFsc28gZm9yIHJlcGVhdGVkIHN1YnRyZWVzIGJ5XG4gICAqIG9iamVjdCBpZGVudGl0eS5cbiAgICpcbiAgICogQXMgYSBiZXN0IGVmZm9ydCBvbmx5IGZvciBkaWFnbm9zdGljIGludGVycHJldGF0aW9uIGJ5IGh1bWFucyxcbiAgICogYGJlc3RFZmZvcnRTdHJpbmdpZnlgIGFsc28gdHVybnMgdmFyaW91cyBjYXNlcyB0aGF0IG5vcm1hbFxuICAgKiBgSlNPTi5zdHJpbmdpZnlgIHNraXBzIG9yIGVycm9ycyBvbiwgbGlrZSBgdW5kZWZpbmVkYCBvciBiaWdpbnRzLFxuICAgKiBpbnRvIHN0cmluZ3MgdGhhdCBjb252ZXkgdGhlaXIgbWVhbmluZy4gVG8gZGlzdGluZ3Vpc2ggdGhpcyBmcm9tXG4gICAqIHN0cmluZ3MgaW4gdGhlIGlucHV0LCB0aGVzZSBzeW50aGVzaXplZCBzdHJpbmdzIGFsd2F5cyBiZWdpbiBhbmRcbiAgICogZW5kIHdpdGggc3F1YXJlIGJyYWNrZXRzLiBUbyBkaXN0aW5ndWlzaCB0aG9zZSBzdHJpbmdzIGZyb20gYW5cbiAgICogaW5wdXQgc3RyaW5nIHdpdGggc3F1YXJlIGJyYWNrZXRzLCBhbmQgaW5wdXQgc3RyaW5nIHRoYXQgc3RhcnRzXG4gICAqIHdpdGggYW4gb3BlbiBzcXVhcmUgYnJhY2tldCBgW2AgaXMgaXRzZWxmIHBsYWNlZCBpbiBzcXVhcmUgYnJhY2tldHMuXG4gICAqXG4gICAqIEBwYXJhbSB7YW55fSBwYXlsb2FkXG4gICAqIEBwYXJhbSB7KHN0cmluZ3xudW1iZXIpPX0gc3BhY2VzXG4gICAqIEByZXR1cm5zIHtzdHJpbmd9XG4gICAqL1xuICBjb25zdCBiZXN0RWZmb3J0U3RyaW5naWZ5ID0gKHBheWxvYWQsIHNwYWNlcyA9IHVuZGVmaW5lZCkgPT4ge1xuICAgIGNvbnN0IHNlZW5TZXQgPSBuZXcgU2V0KCk7XG4gICAgY29uc3QgcmVwbGFjZXIgPSAoXywgdmFsKSA9PiB7XG4gICAgICBzd2l0Y2ggKHR5cGVvZiB2YWwpIHtcbiAgICAgICAgY2FzZSAnb2JqZWN0Jzoge1xuICAgICAgICAgIGlmICh2YWwgPT09IG51bGwpIHtcbiAgICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICAgIH1cbiAgICAgICAgICBpZiAoc2VlblNldC5oYXModmFsKSkge1xuICAgICAgICAgICAgcmV0dXJuICdbU2Vlbl0nO1xuICAgICAgICAgIH1cbiAgICAgICAgICBzZWVuU2V0LmFkZCh2YWwpO1xuICAgICAgICAgIGlmICh2YWwgaW5zdGFuY2VvZiBFcnJvcikge1xuICAgICAgICAgICAgcmV0dXJuIGBbJHt2YWwubmFtZX06ICR7dmFsLm1lc3NhZ2V9XWA7XG4gICAgICAgICAgfVxuICAgICAgICAgIGlmIChTeW1ib2wudG9TdHJpbmdUYWcgaW4gdmFsKSB7XG4gICAgICAgICAgICAvLyBGb3IgdGhlIGJ1aWx0LWlucyB0aGF0IGhhdmUgb3IgaW5oZXJpdCBhIGBTeW1ib2wudG9TdHJpbmdUYWdgLW5hbWVkXG4gICAgICAgICAgICAvLyBwcm9wZXJ0eSwgbW9zdCBvZiB0aGVtIGluaGVyaXQgdGhlIGRlZmF1bHQgYHRvU3RyaW5nYCBtZXRob2QsXG4gICAgICAgICAgICAvLyB3aGljaCB3aWxsIHByaW50IGluIGEgc2ltaWxhciBtYW5uZXI6IGBcIltvYmplY3QgRm9vXVwiYCB2c1xuICAgICAgICAgICAgLy8gYFwiW0Zvb11cImAuIFRoZSBleGNlcHRpb25zIGFyZVxuICAgICAgICAgICAgLy8gICAgKiBgU3ltYm9sLnByb3RvdHlwZWAsIGBCaWdJbnQucHJvdG90eXBlYCwgYFN0cmluZy5wcm90b3R5cGVgXG4gICAgICAgICAgICAvLyAgICAgIHdoaWNoIGRvbid0IG1hdHRlciB0byB1cyBzaW5jZSB3ZSBoYW5kbGUgcHJpbWl0aXZlc1xuICAgICAgICAgICAgLy8gICAgICBzZXBhcmF0ZWx5IGFuZCB3ZSBkb24ndCBjYXJlIGFib3V0IHByaW1pdGl2ZSB3cmFwcGVyIG9iamVjdHMuXG4gICAgICAgICAgICAvLyAgICAqIFRPRE9cbiAgICAgICAgICAgIC8vICAgICAgYERhdGUucHJvdG90eXBlYCwgYFR5cGVkQXJyYXkucHJvdG90eXBlYC5cbiAgICAgICAgICAgIC8vICAgICAgSG1tbSwgd2UgcHJvYmFibHkgc2hvdWxkIG1ha2Ugc3BlY2lhbCBjYXNlcyBmb3IgdGhlc2UuIFdlJ3JlXG4gICAgICAgICAgICAvLyAgICAgIG5vdCB1c2luZyB0aGVzZSB5ZXQsIHNvIGl0J3Mgbm90IHVyZ2VudC4gQnV0IG90aGVycyB3aWxsIHJ1blxuICAgICAgICAgICAgLy8gICAgICBpbnRvIHRoZXNlLlxuICAgICAgICAgICAgLy9cbiAgICAgICAgICAgIC8vIE9uY2UgIzIwMTggaXMgY2xvc2VkLCB0aGUgb25seSBvYmplY3RzIGluIG91ciBjb2RlIHRoYXQgaGF2ZSBvclxuICAgICAgICAgICAgLy8gaW5oZXJpdCBhIGBTeW1ib2wudG9TdHJpbmdUYWdgLW5hbWVkIHByb3BlcnR5IGFyZSByZW1vdGFibGVzXG4gICAgICAgICAgICAvLyBvciB0aGVpciByZW1vdGUgcHJlc2VuY2VzLlxuICAgICAgICAgICAgLy8gVGhpcyBwcmludGluZyB3aWxsIGRvIGEgZ29vZCBqb2IgZm9yIHRoZXNlIHdpdGhvdXRcbiAgICAgICAgICAgIC8vIHZpb2xhdGluZyBhYnN0cmFjdGlvbiBsYXllcmluZy4gVGhpcyBiZWhhdmlvciBtYWtlcyBzZW5zZVxuICAgICAgICAgICAgLy8gcHVyZWx5IGluIHRlcm1zIG9mIEphdmFTY3JpcHQgY29uY2VwdHMuIFRoYXQncyBzb21lIG9mIHRoZVxuICAgICAgICAgICAgLy8gbW90aXZhdGlvbiBmb3IgY2hvb3NpbmcgdGhhdCByZXByZXNlbnRhdGlvbiBvZiByZW1vdGFibGVzXG4gICAgICAgICAgICAvLyBhbmQgdGhlaXIgcmVtb3RlIHByZXNlbmNlcyBpbiB0aGUgZmlyc3QgcGxhY2UuXG4gICAgICAgICAgICByZXR1cm4gYFske3ZhbFtTeW1ib2wudG9TdHJpbmdUYWddfV1gO1xuICAgICAgICAgIH1cbiAgICAgICAgICByZXR1cm4gdmFsO1xuICAgICAgICB9XG4gICAgICAgIGNhc2UgJ2Z1bmN0aW9uJzoge1xuICAgICAgICAgIHJldHVybiBgW0Z1bmN0aW9uICR7dmFsLm5hbWUgfHwgJzxhbm9uPid9XWA7XG4gICAgICAgIH1cbiAgICAgICAgY2FzZSAnc3RyaW5nJzoge1xuICAgICAgICAgIGlmICh2YWwuc3RhcnRzV2l0aCgnWycpKSB7XG4gICAgICAgICAgICByZXR1cm4gYFske3ZhbH1dYDtcbiAgICAgICAgICB9XG4gICAgICAgICAgcmV0dXJuIHZhbDtcbiAgICAgICAgfVxuICAgICAgICBjYXNlICd1bmRlZmluZWQnOlxuICAgICAgICBjYXNlICdzeW1ib2wnOiB7XG4gICAgICAgICAgcmV0dXJuIGBbJHtTdHJpbmcodmFsKX1dYDtcbiAgICAgICAgfVxuICAgICAgICBjYXNlICdiaWdpbnQnOiB7XG4gICAgICAgICAgcmV0dXJuIGBbJHt2YWx9bl1gO1xuICAgICAgICB9XG4gICAgICAgIGNhc2UgJ251bWJlcic6IHtcbiAgICAgICAgICBpZiAoT2JqZWN0LmlzKHZhbCwgTmFOKSkge1xuICAgICAgICAgICAgcmV0dXJuICdbTmFOXSc7XG4gICAgICAgICAgfSBlbHNlIGlmICh2YWwgPT09IEluZmluaXR5KSB7XG4gICAgICAgICAgICByZXR1cm4gJ1tJbmZpbml0eV0nO1xuICAgICAgICAgIH0gZWxzZSBpZiAodmFsID09PSAtSW5maW5pdHkpIHtcbiAgICAgICAgICAgIHJldHVybiAnWy1JbmZpbml0eV0nO1xuICAgICAgICAgIH1cbiAgICAgICAgICByZXR1cm4gdmFsO1xuICAgICAgICB9XG4gICAgICAgIGRlZmF1bHQ6IHtcbiAgICAgICAgICByZXR1cm4gdmFsO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgfTtcbiAgICByZXR1cm4gSlNPTi5zdHJpbmdpZnkocGF5bG9hZCwgcmVwbGFjZXIsIHNwYWNlcyk7XG4gIH07XG4gIGZyZWV6ZShiZXN0RWZmb3J0U3RyaW5naWZ5KTtcblxuICAvLyBDb3B5cmlnaHQgKEMpIDIwMTkgQWdvcmljLCB1bmRlciBBcGFjaGUgTGljZW5zZSAyLjBcblxuICAvLyBGb3Igb3VyIGludGVybmFsIGRlYnVnZ2luZyBwdXJwb3NlcywgdW5jb21tZW50XG4gIC8vIGNvbnN0IGludGVybmFsRGVidWdDb25zb2xlID0gY29uc29sZTtcblxuICAvLyAvLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vL1xuXG4gIC8qKiBAdHlwZSB7V2Vha01hcDxTdHJpbmdhYmxlUGF5bG9hZCwgYW55Pn0gKi9cbiAgY29uc3QgZGVjbGFzc2lmaWVycyA9IG5ldyBXZWFrTWFwKCk7XG5cbiAgLyoqIEB0eXBlIHtBc3NlcnRRdW90ZX0gKi9cbiAgY29uc3QgcXVvdGUgPSAocGF5bG9hZCwgc3BhY2VzID0gdW5kZWZpbmVkKSA9PiB7XG4gICAgY29uc3QgcmVzdWx0ID0gZnJlZXplKHtcbiAgICAgIHRvU3RyaW5nOiBmcmVlemUoKCkgPT4gYmVzdEVmZm9ydFN0cmluZ2lmeShwYXlsb2FkLCBzcGFjZXMpKSxcbiAgICB9KTtcbiAgICBkZWNsYXNzaWZpZXJzLnNldChyZXN1bHQsIHBheWxvYWQpO1xuICAgIHJldHVybiByZXN1bHQ7XG4gIH07XG4gIGZyZWV6ZShxdW90ZSk7XG5cbiAgLy8gLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy9cblxuICAvKipcbiAgICogQHR5cGVkZWYge09iamVjdH0gSGlkZGVuRGV0YWlsc1xuICAgKlxuICAgKiBDYXB0dXJlcyB0aGUgYXJndW1lbnRzIHBhc3NlZCB0byB0aGUgYGRldGFpbHNgIHRlbXBsYXRlIHN0cmluZyB0YWcuXG4gICAqXG4gICAqIEBwcm9wZXJ0eSB7VGVtcGxhdGVTdHJpbmdzQXJyYXkgfCBzdHJpbmdbXX0gdGVtcGxhdGVcbiAgICogQHByb3BlcnR5IHthbnlbXX0gYXJnc1xuICAgKi9cblxuICAvKipcbiAgICogQHR5cGUge1dlYWtNYXA8RGV0YWlsc1Rva2VuLCBIaWRkZW5EZXRhaWxzPn1cbiAgICpcbiAgICogTWFwcyBmcm9tIGEgZGV0YWlscyB0b2tlbiB3aGljaCBhIGBkZXRhaWxzYCB0ZW1wbGF0ZSBsaXRlcmFsIHJldHVybmVkXG4gICAqIHRvIGEgcmVjb3JkIG9mIHRoZSBjb250ZW50cyBvZiB0aGF0IHRlbXBsYXRlIGxpdGVyYWwgZXhwcmVzc2lvbi5cbiAgICovXG4gIGNvbnN0IGhpZGRlbkRldGFpbHNNYXAgPSBuZXcgV2Vha01hcCgpO1xuXG4gIC8qKiBAdHlwZSB7RGV0YWlsc1RhZ30gKi9cbiAgY29uc3QgZGV0YWlscyA9ICh0ZW1wbGF0ZSwgLi4uYXJncykgPT4ge1xuICAgIC8vIEtlZXAgaW4gbWluZCB0aGF0IHRoZSB2YXN0IG1ham9yaXR5IG9mIGNhbGxzIHRvIGBkZXRhaWxzYCBjcmVhdGVzXG4gICAgLy8gYSBkZXRhaWxzIHRva2VuIHRoYXQgaXMgbmV2ZXIgdXNlZCwgc28gdGhpcyBwYXRoIG11c3QgcmVtYWluIGFzIGZhc3QgYXNcbiAgICAvLyBwb3NzaWJsZS4gSGVuY2Ugd2Ugc3RvcmUgd2hhdCB3ZSd2ZSBnb3Qgd2l0aCBsaXR0bGUgcHJvY2Vzc2luZywgcG9zdHBvbmluZ1xuICAgIC8vIGFsbCB0aGUgd29yayB0byBoYXBwZW4gb25seSBpZiBuZWVkZWQsIGZvciBleGFtcGxlLCBpZiBhbiBhc3NlcnRpb24gZmFpbHMuXG4gICAgY29uc3QgZGV0YWlsc1Rva2VuID0gZnJlZXplKHsgX19wcm90b19fOiBudWxsIH0pO1xuICAgIGhpZGRlbkRldGFpbHNNYXAuc2V0KGRldGFpbHNUb2tlbiwgeyB0ZW1wbGF0ZSwgYXJncyB9KTtcbiAgICByZXR1cm4gZGV0YWlsc1Rva2VuO1xuICB9O1xuICBmcmVlemUoZGV0YWlscyk7XG5cbiAgLyoqXG4gICAqIEBwYXJhbSB7SGlkZGVuRGV0YWlsc30gaGlkZGVuRGV0YWlsc1xuICAgKiBAcmV0dXJucyB7c3RyaW5nfVxuICAgKi9cbiAgY29uc3QgZ2V0TWVzc2FnZVN0cmluZyA9ICh7IHRlbXBsYXRlLCBhcmdzIH0pID0+IHtcbiAgICBjb25zdCBwYXJ0cyA9IFt0ZW1wbGF0ZVswXV07XG4gICAgZm9yIChsZXQgaSA9IDA7IGkgPCBhcmdzLmxlbmd0aDsgaSArPSAxKSB7XG4gICAgICBjb25zdCBhcmcgPSBhcmdzW2ldO1xuICAgICAgbGV0IGFyZ1N0cjtcbiAgICAgIGlmIChkZWNsYXNzaWZpZXJzLmhhcyhhcmcpKSB7XG4gICAgICAgIGFyZ1N0ciA9IGAke2FyZ31gO1xuICAgICAgfSBlbHNlIGlmIChhcmcgaW5zdGFuY2VvZiBFcnJvcikge1xuICAgICAgICBhcmdTdHIgPSBgKCR7YW4oYXJnLm5hbWUpfSlgO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgYXJnU3RyID0gYCgke2FuKHR5cGVvZiBhcmcpfSlgO1xuICAgICAgfVxuICAgICAgcGFydHMucHVzaChhcmdTdHIsIHRlbXBsYXRlW2kgKyAxXSk7XG4gICAgfVxuICAgIHJldHVybiBwYXJ0cy5qb2luKCcnKTtcbiAgfTtcblxuICAvKipcbiAgICogQHBhcmFtIHtIaWRkZW5EZXRhaWxzfSBoaWRkZW5EZXRhaWxzXG4gICAqIEByZXR1cm5zIHtMb2dBcmdzfVxuICAgKi9cbiAgY29uc3QgZ2V0TG9nQXJncyA9ICh7IHRlbXBsYXRlLCBhcmdzIH0pID0+IHtcbiAgICBjb25zdCBsb2dBcmdzID0gW3RlbXBsYXRlWzBdXTtcbiAgICBmb3IgKGxldCBpID0gMDsgaSA8IGFyZ3MubGVuZ3RoOyBpICs9IDEpIHtcbiAgICAgIGxldCBhcmcgPSBhcmdzW2ldO1xuICAgICAgaWYgKGRlY2xhc3NpZmllcnMuaGFzKGFyZykpIHtcbiAgICAgICAgYXJnID0gZGVjbGFzc2lmaWVycy5nZXQoYXJnKTtcbiAgICAgIH1cbiAgICAgIC8vIFJlbW92ZSB0aGUgZXh0cmEgc3BhY2VzIChzaW5jZSBjb25zb2xlLmVycm9yIHB1dHMgdGhlbVxuICAgICAgLy8gYmV0d2VlbiBlYWNoIGNhdXNlKS5cbiAgICAgIGNvbnN0IHByaW9yV2l0aG91dFNwYWNlID0gKGxvZ0FyZ3MucG9wKCkgfHwgJycpLnJlcGxhY2UoLyAkLywgJycpO1xuICAgICAgaWYgKHByaW9yV2l0aG91dFNwYWNlICE9PSAnJykge1xuICAgICAgICBsb2dBcmdzLnB1c2gocHJpb3JXaXRob3V0U3BhY2UpO1xuICAgICAgfVxuICAgICAgY29uc3QgbmV4dFdpdGhvdXRTcGFjZSA9IHRlbXBsYXRlW2kgKyAxXS5yZXBsYWNlKC9eIC8sICcnKTtcbiAgICAgIGxvZ0FyZ3MucHVzaChhcmcsIG5leHRXaXRob3V0U3BhY2UpO1xuICAgIH1cbiAgICBpZiAobG9nQXJnc1tsb2dBcmdzLmxlbmd0aCAtIDFdID09PSAnJykge1xuICAgICAgbG9nQXJncy5wb3AoKTtcbiAgICB9XG4gICAgcmV0dXJuIGxvZ0FyZ3M7XG4gIH07XG5cbiAgLyoqXG4gICAqIEB0eXBlIHtXZWFrTWFwPEVycm9yLCBMb2dBcmdzPn1cbiAgICpcbiAgICogTWFwcyBmcm9tIGFuIGVycm9yIG9iamVjdCB0byB0aGUgbG9nIGFyZ3MgdGhhdCBhcmUgYSBtb3JlIGluZm9ybWF0aXZlXG4gICAqIGFsdGVybmF0aXZlIG1lc3NhZ2UgZm9yIHRoYXQgZXJyb3IuIFdoZW4gbG9nZ2luZyB0aGUgZXJyb3IsIHRoZXNlXG4gICAqIGxvZyBhcmdzIHNob3VsZCBiZSBwcmVmZXJyZWQgdG8gYGVycm9yLm1lc3NhZ2VgLlxuICAgKi9cbiAgY29uc3QgaGlkZGVuTWVzc2FnZUxvZ0FyZ3MgPSBuZXcgV2Vha01hcCgpO1xuXG4gIC8qKlxuICAgKiBAdHlwZSB7QXNzZXJ0TWFrZUVycm9yfVxuICAgKi9cbiAgY29uc3QgbWFrZUVycm9yID0gKFxuICAgIG9wdERldGFpbHMgPSBkZXRhaWxzYEFzc2VydCBmYWlsZWRgLFxuICAgIEVycm9yQ29uc3RydWN0b3IgPSBFcnJvcixcbiAgKSA9PiB7XG4gICAgaWYgKHR5cGVvZiBvcHREZXRhaWxzID09PSAnc3RyaW5nJykge1xuICAgICAgLy8gSWYgaXQgaXMgYSBzdHJpbmcsIHVzZSBpdCBhcyB0aGUgbGl0ZXJhbCBwYXJ0IG9mIHRoZSB0ZW1wbGF0ZSBzb1xuICAgICAgLy8gaXQgZG9lc24ndCBnZXQgcXVvdGVkLlxuICAgICAgb3B0RGV0YWlscyA9IGRldGFpbHMoW29wdERldGFpbHNdKTtcbiAgICB9XG4gICAgY29uc3QgaGlkZGVuRGV0YWlscyA9IGhpZGRlbkRldGFpbHNNYXAuZ2V0KG9wdERldGFpbHMpO1xuICAgIGlmIChoaWRkZW5EZXRhaWxzID09PSB1bmRlZmluZWQpIHtcbiAgICAgIHRocm93IG5ldyBFcnJvcihgdW5yZWNvZ25pemVkIGRldGFpbHMgJHtvcHREZXRhaWxzfWApO1xuICAgIH1cbiAgICBjb25zdCBtZXNzYWdlU3RyaW5nID0gZ2V0TWVzc2FnZVN0cmluZyhoaWRkZW5EZXRhaWxzKTtcbiAgICBjb25zdCBlcnJvciA9IG5ldyBFcnJvckNvbnN0cnVjdG9yKG1lc3NhZ2VTdHJpbmcpO1xuICAgIGhpZGRlbk1lc3NhZ2VMb2dBcmdzLnNldChlcnJvciwgZ2V0TG9nQXJncyhoaWRkZW5EZXRhaWxzKSk7XG4gICAgLy8gVGhlIG5leHQgbGluZSBpcyBhIHBhcnRpY3VsYXJseSBmcnVpdGZ1bCBwbGFjZSB0byBwdXQgYSBicmVha3BvaW50LlxuICAgIHJldHVybiBlcnJvcjtcbiAgfTtcbiAgZnJlZXplKG1ha2VFcnJvcik7XG5cbiAgLy8gLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy9cblxuICAvKipcbiAgICogQHR5cGUge1dlYWtNYXA8RXJyb3IsIExvZ0FyZ3NbXT59XG4gICAqXG4gICAqIE1hcHMgZnJvbSBhbiBlcnJvciB0byBhbiBhcnJheSBvZiBsb2cgYXJncywgd2hlcmUgZWFjaCBsb2cgYXJncyBpc1xuICAgKiByZW1lbWJlcmVkIGFzIGFuIGFubm90YXRpb24gb24gdGhhdCBlcnJvci4gVGhpcyBjYW4gYmUgdXNlZCwgZm9yIGV4YW1wbGUsXG4gICAqIHRvIGtlZXAgdHJhY2sgb2YgYWRkaXRpb25hbCBjYXVzZXMgb2YgdGhlIGVycm9yLiBUaGUgZWxlbWVudHMgb2YgYW55XG4gICAqIGxvZyBhcmdzIG1heSBpbmNsdWRlIGVycm9ycyB3aGljaCBhcmUgYXNzb2NpYXRlZCB3aXRoIGZ1cnRoZXIgYW5ub3RhdGlvbnMuXG4gICAqIEFuIGF1Z21lbnRlZCBjb25zb2xlLCBsaWtlIHRoZSBjYXVzYWwgY29uc29sZSBvZiBgY29uc29sZS5qc2AsIGNvdWxkXG4gICAqIHRoZW4gcmV0cmlldmUgdGhlIGdyYXBoIG9mIHN1Y2ggYW5ub3RhdGlvbnMuXG4gICAqL1xuICBjb25zdCBoaWRkZW5Ob3RlTG9nQXJnc0FycmF5cyA9IG5ldyBXZWFrTWFwKCk7XG5cbiAgLyoqXG4gICAqIEB0eXBlIHtXZWFrTWFwPEVycm9yLCBOb3RlQ2FsbGJhY2tbXT59XG4gICAqXG4gICAqIEFuIGF1Z21lbnRlZCBjb25zb2xlIHdpbGwgbm9ybWFsbHkgb25seSB0YWtlIHRoZSBoaWRkZW4gbm90ZUFyZ3MgYXJyYXkgb25jZSxcbiAgICogd2hlbiBpdCBsb2dzIHRoZSBlcnJvciBiZWluZyBhbm5vdGF0ZWQuIE9uY2UgdGhhdCBoYXBwZW5zLCBmdXJ0aGVyXG4gICAqIGFubm90YXRpb25zIG9mIHRoYXQgZXJyb3Igc2hvdWxkIGdvIHRvIHRoZSBjb25zb2xlIGltbWVkaWF0ZWx5LiBXZSBhcnJhbmdlXG4gICAqIHRoYXQgYnkgYWNjZXB0aW5nIGEgbm90ZS1jYWxsYmFjayBmdW5jdGlvbiBmcm9tIHRoZSBjb25zb2xlIGFzIGFuIG9wdGlvbmFsXG4gICAqIHBhcnQgb2YgdGhhdCB0YWtpbmcgb3BlcmF0aW9uLiBOb3JtYWxseSB0aGVyZSB3aWxsIG9ubHkgYmUgYXQgbW9zdCBvbmVcbiAgICogY2FsbGJhY2sgcGVyIGVycm9yLCBidXQgdGhhdCBkZXBlbmRzIG9uIGNvbnNvbGUgYmVoYXZpb3Igd2hpY2ggd2Ugc2hvdWxkIG5vdFxuICAgKiBhc3N1bWUuIFdlIG1ha2UgdGhpcyBhbiBhcnJheSBvZiBjYWxsYmFja3Mgc28gbXVsdGlwbGUgcmVnaXN0cmF0aW9uc1xuICAgKiBhcmUgaW5kZXBlbmRlbnQuXG4gICAqL1xuICBjb25zdCBoaWRkZW5Ob3RlQ2FsbGJhY2tBcnJheXMgPSBuZXcgV2Vha01hcCgpO1xuXG4gIC8qKiBAdHlwZSB7QXNzZXJ0Tm90ZX0gKi9cbiAgY29uc3Qgbm90ZSA9IChlcnJvciwgZGV0YWlsc05vdGUpID0+IHtcbiAgICBpZiAodHlwZW9mIGRldGFpbHNOb3RlID09PSAnc3RyaW5nJykge1xuICAgICAgLy8gSWYgaXQgaXMgYSBzdHJpbmcsIHVzZSBpdCBhcyB0aGUgbGl0ZXJhbCBwYXJ0IG9mIHRoZSB0ZW1wbGF0ZSBzb1xuICAgICAgLy8gaXQgZG9lc24ndCBnZXQgcXVvdGVkLlxuICAgICAgZGV0YWlsc05vdGUgPSBkZXRhaWxzKFtkZXRhaWxzTm90ZV0pO1xuICAgIH1cbiAgICBjb25zdCBoaWRkZW5EZXRhaWxzID0gaGlkZGVuRGV0YWlsc01hcC5nZXQoZGV0YWlsc05vdGUpO1xuICAgIGlmIChoaWRkZW5EZXRhaWxzID09PSB1bmRlZmluZWQpIHtcbiAgICAgIHRocm93IG5ldyBFcnJvcihgdW5yZWNvZ25pemVkIGRldGFpbHMgJHtkZXRhaWxzTm90ZX1gKTtcbiAgICB9XG4gICAgY29uc3QgbG9nQXJncyA9IGdldExvZ0FyZ3MoaGlkZGVuRGV0YWlscyk7XG4gICAgY29uc3QgY2FsbGJhY2tzID0gaGlkZGVuTm90ZUNhbGxiYWNrQXJyYXlzLmdldChlcnJvcik7XG4gICAgaWYgKGNhbGxiYWNrcyAhPT0gdW5kZWZpbmVkKSB7XG4gICAgICBmb3IgKGNvbnN0IGNhbGxiYWNrIG9mIGNhbGxiYWNrcykge1xuICAgICAgICBjYWxsYmFjayhlcnJvciwgbG9nQXJncyk7XG4gICAgICB9XG4gICAgfSBlbHNlIHtcbiAgICAgIGNvbnN0IGxvZ0FyZ3NBcnJheSA9IGhpZGRlbk5vdGVMb2dBcmdzQXJyYXlzLmdldChlcnJvcik7XG4gICAgICBpZiAobG9nQXJnc0FycmF5ICE9PSB1bmRlZmluZWQpIHtcbiAgICAgICAgbG9nQXJnc0FycmF5LnB1c2gobG9nQXJncyk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBoaWRkZW5Ob3RlTG9nQXJnc0FycmF5cy5zZXQoZXJyb3IsIFtsb2dBcmdzXSk7XG4gICAgICB9XG4gICAgfVxuICB9O1xuICBmcmVlemUobm90ZSk7XG5cbiAgLyoqXG4gICAqIFRoZSB1bnByaXZpbGVnZWQgZm9ybSB0aGF0IGp1c3QgdXNlcyB0aGUgZGUgZmFjdG8gYGVycm9yLnN0YWNrYCBwcm9wZXJ0eS5cbiAgICogVGhlIHN0YXJ0IGNvbXBhcnRtZW50IG5vcm1hbGx5IGhhcyBhIHByaXZpbGVnZWQgYGdsb2JhbFRoaXMuZ2V0U3RhY2tTdHJpbmdgXG4gICAqIHdoaWNoIHNob3VsZCBiZSBwcmVmZXJyZWQgaWYgcHJlc2VudC5cbiAgICpcbiAgICogQHBhcmFtIHtFcnJvcn0gZXJyb3JcbiAgICogQHJldHVybnMge3N0cmluZ31cbiAgICovXG4gIGNvbnN0IGRlZmF1bHRHZXRTdGFja1N0cmluZyA9IGVycm9yID0+IHtcbiAgICBpZiAoISgnc3RhY2snIGluIGVycm9yKSkge1xuICAgICAgcmV0dXJuICcnO1xuICAgIH1cbiAgICBjb25zdCBzdGFja1N0cmluZyA9IGAke2Vycm9yLnN0YWNrfWA7XG4gICAgY29uc3QgcG9zID0gc3RhY2tTdHJpbmcuaW5kZXhPZignXFxuJyk7XG4gICAgaWYgKHN0YWNrU3RyaW5nLnN0YXJ0c1dpdGgoJyAnKSB8fCBwb3MgPT09IC0xKSB7XG4gICAgICByZXR1cm4gc3RhY2tTdHJpbmc7XG4gICAgfVxuICAgIHJldHVybiBzdGFja1N0cmluZy5zbGljZShwb3MgKyAxKTsgLy8gZXhjbHVkZSB0aGUgaW5pdGlhbCBuZXdsaW5lXG4gIH07XG5cbiAgLyoqIEB0eXBlIHtMb2dnZWRFcnJvckhhbmRsZXJ9ICovXG4gIGNvbnN0IGxvZ2dlZEVycm9ySGFuZGxlciA9IHtcbiAgICBnZXRTdGFja1N0cmluZzogZ2xvYmFsVGhpcy5nZXRTdGFja1N0cmluZyB8fCBkZWZhdWx0R2V0U3RhY2tTdHJpbmcsXG4gICAgdGFrZU1lc3NhZ2VMb2dBcmdzOiBlcnJvciA9PiB7XG4gICAgICBjb25zdCByZXN1bHQgPSBoaWRkZW5NZXNzYWdlTG9nQXJncy5nZXQoZXJyb3IpO1xuICAgICAgaGlkZGVuTWVzc2FnZUxvZ0FyZ3MuZGVsZXRlKGVycm9yKTtcbiAgICAgIHJldHVybiByZXN1bHQ7XG4gICAgfSxcbiAgICB0YWtlTm90ZUxvZ0FyZ3NBcnJheTogKGVycm9yLCBjYWxsYmFjaykgPT4ge1xuICAgICAgY29uc3QgcmVzdWx0ID0gaGlkZGVuTm90ZUxvZ0FyZ3NBcnJheXMuZ2V0KGVycm9yKTtcbiAgICAgIGhpZGRlbk5vdGVMb2dBcmdzQXJyYXlzLmRlbGV0ZShlcnJvcik7XG4gICAgICBpZiAoY2FsbGJhY2sgIT09IHVuZGVmaW5lZCkge1xuICAgICAgICBjb25zdCBjYWxsYmFja3MgPSBoaWRkZW5Ob3RlQ2FsbGJhY2tBcnJheXMuZ2V0KGVycm9yKTtcbiAgICAgICAgaWYgKGNhbGxiYWNrcykge1xuICAgICAgICAgIGNhbGxiYWNrcy5wdXNoKGNhbGxiYWNrKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBoaWRkZW5Ob3RlQ2FsbGJhY2tBcnJheXMuc2V0KGVycm9yLCBbY2FsbGJhY2tdKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgcmV0dXJuIHJlc3VsdCB8fCBbXTtcbiAgICB9LFxuICB9O1xuICBmcmVlemUobG9nZ2VkRXJyb3JIYW5kbGVyKTtcblxuICAvLyAvLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vL1xuXG4gIC8qKlxuICAgKiBAdHlwZSB7TWFrZUFzc2VydH1cbiAgICovXG4gIGNvbnN0IG1ha2VBc3NlcnQgPSAob3B0UmFpc2UgPSB1bmRlZmluZWQpID0+IHtcbiAgICAvKiogQHR5cGUge0Fzc2VydEZhaWx9ICovXG4gICAgY29uc3QgZmFpbCA9IChcbiAgICAgIG9wdERldGFpbHMgPSBkZXRhaWxzYEFzc2VydCBmYWlsZWRgLFxuICAgICAgRXJyb3JDb25zdHJ1Y3RvciA9IEVycm9yLFxuICAgICkgPT4ge1xuICAgICAgY29uc3QgcmVhc29uID0gbWFrZUVycm9yKG9wdERldGFpbHMsIEVycm9yQ29uc3RydWN0b3IpO1xuICAgICAgaWYgKG9wdFJhaXNlICE9PSB1bmRlZmluZWQpIHtcbiAgICAgICAgb3B0UmFpc2UocmVhc29uKTtcbiAgICAgIH1cbiAgICAgIHRocm93IHJlYXNvbjtcbiAgICB9O1xuICAgIGZyZWV6ZShmYWlsKTtcblxuICAgIC8vIERvbid0IGZyZWV6ZSBvciBleHBvcnQgYGJhc2VBc3NlcnRgIHVudGlsIHdlIGFkZCBtZXRob2RzLlxuICAgIC8vIFRPRE8gSWYgSSBjaGFuZ2UgdGhpcyBmcm9tIGEgYGZ1bmN0aW9uYCBmdW5jdGlvbiB0byBhbiBhcnJvd1xuICAgIC8vIGZ1bmN0aW9uLCBJIHNlZW0gdG8gZ2V0IHR5cGUgZXJyb3JzIGZyb20gVHlwZVNjcmlwdC4gV2h5P1xuICAgIC8qKiBAdHlwZSB7QmFzZUFzc2VydH0gKi9cbiAgICBmdW5jdGlvbiBiYXNlQXNzZXJ0KFxuICAgICAgZmxhZyxcbiAgICAgIG9wdERldGFpbHMgPSBkZXRhaWxzYENoZWNrIGZhaWxlZGAsXG4gICAgICBFcnJvckNvbnN0cnVjdG9yID0gRXJyb3IsXG4gICAgKSB7XG4gICAgICBpZiAoIWZsYWcpIHtcbiAgICAgICAgdGhyb3cgZmFpbChvcHREZXRhaWxzLCBFcnJvckNvbnN0cnVjdG9yKTtcbiAgICAgIH1cbiAgICB9XG5cbiAgICAvKiogQHR5cGUge0Fzc2VydEVxdWFsfSAqL1xuICAgIGNvbnN0IGVxdWFsID0gKFxuICAgICAgYWN0dWFsLFxuICAgICAgZXhwZWN0ZWQsXG4gICAgICBvcHREZXRhaWxzID0gZGV0YWlsc2BFeHBlY3RlZCAke2FjdHVhbH0gaXMgc2FtZSBhcyAke2V4cGVjdGVkfWAsXG4gICAgICBFcnJvckNvbnN0cnVjdG9yID0gUmFuZ2VFcnJvcixcbiAgICApID0+IHtcbiAgICAgIGJhc2VBc3NlcnQoaXMoYWN0dWFsLCBleHBlY3RlZCksIG9wdERldGFpbHMsIEVycm9yQ29uc3RydWN0b3IpO1xuICAgIH07XG4gICAgZnJlZXplKGVxdWFsKTtcblxuICAgIC8qKiBAdHlwZSB7QXNzZXJ0VHlwZW9mfSAqL1xuICAgIGNvbnN0IGFzc2VydFR5cGVvZiA9IChzcGVjaW1lbiwgdHlwZW5hbWUsIG9wdERldGFpbHMpID0+IHtcbiAgICAgIGJhc2VBc3NlcnQoXG4gICAgICAgIHR5cGVvZiB0eXBlbmFtZSA9PT0gJ3N0cmluZycsXG4gICAgICAgIGRldGFpbHNgJHtxdW90ZSh0eXBlbmFtZSl9IG11c3QgYmUgYSBzdHJpbmdgLFxuICAgICAgKTtcbiAgICAgIGlmIChvcHREZXRhaWxzID09PSB1bmRlZmluZWQpIHtcbiAgICAgICAgLy8gTGlrZVxuICAgICAgICAvLyBgYGBqc1xuICAgICAgICAvLyBvcHREZXRhaWxzID0gZGV0YWlsc2Ake3NwZWNpbWVufSBtdXN0IGJlICR7cXVvdGUoYW4odHlwZW5hbWUpKX1gO1xuICAgICAgICAvLyBgYGBcbiAgICAgICAgLy8gZXhjZXB0IGl0IHB1dHMgdGhlIHR5cGVuYW1lIGludG8gdGhlIGxpdGVyYWwgcGFydCBvZiB0aGUgdGVtcGxhdGVcbiAgICAgICAgLy8gc28gaXQgZG9lc24ndCBnZXQgcXVvdGVkLlxuICAgICAgICBvcHREZXRhaWxzID0gZGV0YWlscyhbJycsIGAgbXVzdCBiZSAke2FuKHR5cGVuYW1lKX1gXSwgc3BlY2ltZW4pO1xuICAgICAgfVxuICAgICAgZXF1YWwodHlwZW9mIHNwZWNpbWVuLCB0eXBlbmFtZSwgb3B0RGV0YWlscywgVHlwZUVycm9yKTtcbiAgICB9O1xuICAgIGZyZWV6ZShhc3NlcnRUeXBlb2YpO1xuXG4gICAgLyoqIEB0eXBlIHtBc3NlcnRTdHJpbmd9ICovXG4gICAgY29uc3QgYXNzZXJ0U3RyaW5nID0gKHNwZWNpbWVuLCBvcHREZXRhaWxzKSA9PlxuICAgICAgYXNzZXJ0VHlwZW9mKHNwZWNpbWVuLCAnc3RyaW5nJywgb3B0RGV0YWlscyk7XG5cbiAgICAvLyBOb3RlIHRoYXQgXCJhc3NlcnQgPT09IGJhc2VBc3NlcnRcIlxuICAgIC8qKiBAdHlwZSB7QXNzZXJ0fSAqL1xuICAgIGNvbnN0IGFzc2VydCA9IGFzc2lnbihiYXNlQXNzZXJ0LCB7XG4gICAgICBlcnJvcjogbWFrZUVycm9yLFxuICAgICAgZmFpbCxcbiAgICAgIGVxdWFsLFxuICAgICAgdHlwZW9mOiBhc3NlcnRUeXBlb2YsXG4gICAgICBzdHJpbmc6IGFzc2VydFN0cmluZyxcbiAgICAgIG5vdGUsXG4gICAgICBkZXRhaWxzLFxuICAgICAgcXVvdGUsXG4gICAgICBtYWtlQXNzZXJ0LFxuICAgIH0pO1xuICAgIHJldHVybiBmcmVlemUoYXNzZXJ0KTtcbiAgfTtcbiAgZnJlZXplKG1ha2VBc3NlcnQpO1xuXG4gIC8qKiBAdHlwZSB7QXNzZXJ0fSAqL1xuICBjb25zdCBhc3NlcnQgPSBtYWtlQXNzZXJ0KCk7XG5cbiAgY29uc3QgeyBkZXRhaWxzOiBkLCBxdW90ZTogcSB9ID0gYXNzZXJ0O1xuXG4gIGNvbnN0IGxvY2FsZVBhdHRlcm4gPSAvXihcXHcqW2Etel0pTG9jYWxlKFtBLVpdXFx3KikkLztcblxuICAvLyBVc2UgY29uY2lzZSBtZXRob2RzIHRvIG9idGFpbiBuYW1lZCBmdW5jdGlvbnMgd2l0aG91dCBjb25zdHJ1Y3RvclxuICAvLyBiZWhhdmlvciBvciBgLnByb3RvdHlwZWAgcHJvcGVydHkuXG4gIGNvbnN0IHRhbWVkTWV0aG9kcyA9IHtcbiAgICAvLyBTZWUgaHR0cHM6Ly90YzM5LmVzL2VjbWEyNjIvI3NlYy1zdHJpbmcucHJvdG90eXBlLmxvY2FsZWNvbXBhcmVcbiAgICBsb2NhbGVDb21wYXJlKHRoYXQpIHtcbiAgICAgIGlmICh0aGlzID09PSBudWxsIHx8IHRoaXMgPT09IHVuZGVmaW5lZCkge1xuICAgICAgICB0aHJvdyBuZXcgVHlwZUVycm9yKFxuICAgICAgICAgICdDYW5ub3QgbG9jYWxlQ29tcGFyZSB3aXRoIG51bGwgb3IgdW5kZWZpbmVkIFwidGhpc1wiIHZhbHVlJyxcbiAgICAgICAgKTtcbiAgICAgIH1cbiAgICAgIGNvbnN0IHMgPSBgJHt0aGlzfWA7XG4gICAgICB0aGF0ID0gYCR7dGhhdH1gO1xuICAgICAgaWYgKHMgPCB0aGF0KSB7XG4gICAgICAgIHJldHVybiAtMTtcbiAgICAgIH1cbiAgICAgIGlmIChzID4gdGhhdCkge1xuICAgICAgICByZXR1cm4gMTtcbiAgICAgIH1cbiAgICAgIGFzc2VydChzID09PSB0aGF0LCBkYGV4cGVjdGVkICR7cShzKX0gYW5kICR7cSh0aGF0KX0gdG8gY29tcGFyZWApO1xuICAgICAgcmV0dXJuIDA7XG4gICAgfSxcbiAgfTtcblxuICBjb25zdCBub25Mb2NhbGVDb21wYXJlID0gdGFtZWRNZXRob2RzLmxvY2FsZUNvbXBhcmU7XG5cbiAgZnVuY3Rpb24gdGFtZUxvY2FsZU1ldGhvZHMoaW50cmluc2ljcywgbG9jYWxlVGFtaW5nID0gJ3NhZmUnKSB7XG4gICAgaWYgKGxvY2FsZVRhbWluZyAhPT0gJ3NhZmUnICYmIGxvY2FsZVRhbWluZyAhPT0gJ3Vuc2FmZScpIHtcbiAgICAgIHRocm93IG5ldyBFcnJvcihgdW5yZWNvZ25pemVkIGRhdGVUYW1pbmcgJHtsb2NhbGVUYW1pbmd9YCk7XG4gICAgfVxuICAgIGlmIChsb2NhbGVUYW1pbmcgPT09ICd1bnNhZmUnKSB7XG4gICAgICByZXR1cm47XG4gICAgfVxuXG4gICAgZGVmaW5lUHJvcGVydHkoU3RyaW5nLnByb3RvdHlwZSwgJ2xvY2FsZUNvbXBhcmUnLCB7XG4gICAgICB2YWx1ZTogbm9uTG9jYWxlQ29tcGFyZSxcbiAgICB9KTtcblxuICAgIGZvciAoY29uc3QgaW50cmluc2ljTmFtZSBvZiBnZXRPd25Qcm9wZXJ0eU5hbWVzKGludHJpbnNpY3MpKSB7XG4gICAgICBjb25zdCBpbnRyaW5zaWMgPSBpbnRyaW5zaWNzW2ludHJpbnNpY05hbWVdO1xuICAgICAgaWYgKGludHJpbnNpYyA9PT0gT2JqZWN0KGludHJpbnNpYykpIHtcbiAgICAgICAgZm9yIChjb25zdCBtZXRob2ROYW1lIG9mIGdldE93blByb3BlcnR5TmFtZXMoaW50cmluc2ljKSkge1xuICAgICAgICAgIGNvbnN0IG1hdGNoID0gbG9jYWxlUGF0dGVybi5leGVjKG1ldGhvZE5hbWUpO1xuICAgICAgICAgIGlmIChtYXRjaCkge1xuICAgICAgICAgICAgYXNzZXJ0KFxuICAgICAgICAgICAgICB0eXBlb2YgaW50cmluc2ljW21ldGhvZE5hbWVdID09PSAnZnVuY3Rpb24nLFxuICAgICAgICAgICAgICBkYGV4cGVjdGVkICR7cShtZXRob2ROYW1lKX0gdG8gYmUgYSBmdW5jdGlvbmAsXG4gICAgICAgICAgICApO1xuICAgICAgICAgICAgY29uc3Qgbm9uTG9jYWxlTWV0aG9kTmFtZSA9IGAke21hdGNoWzFdfSR7bWF0Y2hbMl19YDtcbiAgICAgICAgICAgIGNvbnN0IG1ldGhvZCA9IGludHJpbnNpY1tub25Mb2NhbGVNZXRob2ROYW1lXTtcbiAgICAgICAgICAgIGFzc2VydChcbiAgICAgICAgICAgICAgdHlwZW9mIG1ldGhvZCA9PT0gJ2Z1bmN0aW9uJyxcbiAgICAgICAgICAgICAgZGBmdW5jdGlvbiAke3Eobm9uTG9jYWxlTWV0aG9kTmFtZSl9IG5vdCBmb3VuZGAsXG4gICAgICAgICAgICApO1xuICAgICAgICAgICAgZGVmaW5lUHJvcGVydHkoaW50cmluc2ljLCBtZXRob2ROYW1lLCB7IHZhbHVlOiBtZXRob2QgfSk7XG4gICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICB9XG4gICAgfVxuICB9XG5cbiAgLyoqXG4gICAqIGtleXdvcmRzXG4gICAqIEluIEphdmFTY3JpcHQgeW91IGNhbm5vdCB1c2UgdGhlc2UgcmVzZXJ2ZWQgd29yZHMgYXMgdmFyaWFibGVzLlxuICAgKiBTZWUgMTEuNi4xIElkZW50aWZpZXIgTmFtZXNcbiAgICovXG4gIGNvbnN0IGtleXdvcmRzID0gW1xuICAgIC8vIDExLjYuMi4xIEtleXdvcmRzXG4gICAgJ2F3YWl0JyxcbiAgICAnYnJlYWsnLFxuICAgICdjYXNlJyxcbiAgICAnY2F0Y2gnLFxuICAgICdjbGFzcycsXG4gICAgJ2NvbnN0JyxcbiAgICAnY29udGludWUnLFxuICAgICdkZWJ1Z2dlcicsXG4gICAgJ2RlZmF1bHQnLFxuICAgICdkZWxldGUnLFxuICAgICdkbycsXG4gICAgJ2Vsc2UnLFxuICAgICdleHBvcnQnLFxuICAgICdleHRlbmRzJyxcbiAgICAnZmluYWxseScsXG4gICAgJ2ZvcicsXG4gICAgJ2Z1bmN0aW9uJyxcbiAgICAnaWYnLFxuICAgICdpbXBvcnQnLFxuICAgICdpbicsXG4gICAgJ2luc3RhbmNlb2YnLFxuICAgICduZXcnLFxuICAgICdyZXR1cm4nLFxuICAgICdzdXBlcicsXG4gICAgJ3N3aXRjaCcsXG4gICAgJ3RoaXMnLFxuICAgICd0aHJvdycsXG4gICAgJ3RyeScsXG4gICAgJ3R5cGVvZicsXG4gICAgJ3ZhcicsXG4gICAgJ3ZvaWQnLFxuICAgICd3aGlsZScsXG4gICAgJ3dpdGgnLFxuICAgICd5aWVsZCcsXG5cbiAgICAvLyBBbHNvIHJlc2VydmVkIHdoZW4gcGFyc2luZyBzdHJpY3QgbW9kZSBjb2RlXG4gICAgJ2xldCcsXG4gICAgJ3N0YXRpYycsXG5cbiAgICAvLyAxMS42LjIuMiBGdXR1cmUgUmVzZXJ2ZWQgV29yZHNcbiAgICAnZW51bScsXG5cbiAgICAvLyBBbHNvIHJlc2VydmVkIHdoZW4gcGFyc2luZyBzdHJpY3QgbW9kZSBjb2RlXG4gICAgJ2ltcGxlbWVudHMnLFxuICAgICdwYWNrYWdlJyxcbiAgICAncHJvdGVjdGVkJyxcbiAgICAnaW50ZXJmYWNlJyxcbiAgICAncHJpdmF0ZScsXG4gICAgJ3B1YmxpYycsXG5cbiAgICAvLyBSZXNlcnZlZCBidXQgbm90IG1lbnRpb25lZCBpbiBzcGVjc1xuICAgICdhd2FpdCcsXG5cbiAgICAnbnVsbCcsXG4gICAgJ3RydWUnLFxuICAgICdmYWxzZScsXG5cbiAgICAndGhpcycsXG4gICAgJ2FyZ3VtZW50cycsXG4gIF07XG5cbiAgLyoqXG4gICAqIGlkZW50aWZpZXJQYXR0ZXJuXG4gICAqIFNpbXBsaWZpZWQgdmFsaWRhdGlvbiBvZiBpbmRlbnRpZmllciBuYW1lczogbWF5IG9ubHkgY29udGFpbiBhbHBoYW51bWVyaWNcbiAgICogY2hhcmFjdGVycyAob3IgXCIkXCIgb3IgXCJfXCIpLCBhbmQgbWF5IG5vdCBzdGFydCB3aXRoIGEgZGlnaXQuIFRoaXMgaXMgc2FmZVxuICAgKiBhbmQgZG9lcyBub3QgcmVkdWNlcyB0aGUgY29tcGF0aWJpbGl0eSBvZiB0aGUgc2hpbS4gVGhlIG1vdGl2YXRpb24gZm9yXG4gICAqIHRoaXMgbGltaXRhdGlvbiB3YXMgdG8gZGVjcmVhc2UgdGhlIGNvbXBsZXhpdHkgb2YgdGhlIGltcGxlbWVudGF0aW9uLFxuICAgKiBhbmQgdG8gbWFpbnRhaW4gYSByZXNvbmFibGUgbGV2ZWwgb2YgcGVyZm9ybWFuY2UuXG4gICAqIE5vdGU6IFxcdyBpcyBlcXVpdmFsZW50IFthLXpBLVpfMC05XVxuICAgKiBTZWUgMTEuNi4xIElkZW50aWZpZXIgTmFtZXNcbiAgICovXG4gIGNvbnN0IGlkZW50aWZpZXJQYXR0ZXJuID0gbmV3IFJlZ0V4cCgnXlthLXpBLVpfJF1bXFxcXHckXSokJyk7XG5cbiAgLyoqXG4gICAqIGlzVmFsaWRJZGVudGlmaWVyTmFtZSgpXG4gICAqIFdoYXQgdmFyaWFibGUgbmFtZXMgbWlnaHQgaXQgYnJpbmcgaW50byBzY29wZT8gVGhlc2UgaW5jbHVkZSBhbGxcbiAgICogcHJvcGVydHkgbmFtZXMgd2hpY2ggY2FuIGJlIHZhcmlhYmxlIG5hbWVzLCBpbmNsdWRpbmcgdGhlIG5hbWVzXG4gICAqIG9mIGluaGVyaXRlZCBwcm9wZXJ0aWVzLiBJdCBleGNsdWRlcyBzeW1ib2xzIGFuZCBuYW1lcyB3aGljaCBhcmVcbiAgICoga2V5d29yZHMuIFdlIGRyb3Agc3ltYm9scyBzYWZlbHkuIEN1cnJlbnRseSwgdGhpcyBzaGltIHJlZnVzZXNcbiAgICogc2VydmljZSBpZiBhbnkgb2YgdGhlIG5hbWVzIGFyZSBrZXl3b3JkcyBvciBrZXl3b3JkLWxpa2UuIFRoaXMgaXNcbiAgICogc2FmZSBhbmQgb25seSBwcmV2ZW50IHBlcmZvcm1hbmNlIG9wdGltaXphdGlvbi5cbiAgICpcbiAgICogQHBhcmFtIHtzdHJpbmd9IG5hbWVcbiAgICovXG4gIGZ1bmN0aW9uIGlzVmFsaWRJZGVudGlmaWVyTmFtZShuYW1lKSB7XG4gICAgLy8gRW5zdXJlIHdlIGhhdmUgYSB2YWxpZCBpZGVudGlmaWVyLiBXZSB1c2UgcmVnZXhwVGVzdCByYXRoZXIgdGhhblxuICAgIC8vIC8uLi8udGVzdCgpIHRvIGd1YXJkIGFnYWluc3QgdGhlIGNhc2Ugd2hlcmUgUmVnRXhwIGhhcyBiZWVuIHBvaXNvbmVkLlxuICAgIHJldHVybiAoXG4gICAgICBuYW1lICE9PSAnZXZhbCcgJiZcbiAgICAgICFhcnJheUluY2x1ZGVzKGtleXdvcmRzLCBuYW1lKSAmJlxuICAgICAgcmVnZXhwVGVzdChpZGVudGlmaWVyUGF0dGVybiwgbmFtZSlcbiAgICApO1xuICB9XG5cbiAgLypcbiAgICogaXNJbW11dGFibGVEYXRhUHJvcGVydHlcbiAgICovXG5cbiAgZnVuY3Rpb24gaXNJbW11dGFibGVEYXRhUHJvcGVydHkob2JqLCBuYW1lKSB7XG4gICAgY29uc3QgZGVzYyA9IGdldE93blByb3BlcnR5RGVzY3JpcHRvcihvYmosIG5hbWUpO1xuICAgIHJldHVybiAoXG4gICAgICAvL1xuICAgICAgLy8gVGhlIGdldHRlcnMgd2lsbCBub3QgaGF2ZSAud3JpdGFibGUsIGRvbid0IGxldCB0aGUgZmFsc3luZXNzIG9mXG4gICAgICAvLyAndW5kZWZpbmVkJyB0cmljayB1czogdGVzdCB3aXRoID09PSBmYWxzZSwgbm90ICEgLiBIb3dldmVyIGRlc2NyaXB0b3JzXG4gICAgICAvLyBpbmhlcml0IGZyb20gdGhlIChwb3RlbnRpYWxseSBwb2lzb25lZCkgZ2xvYmFsIG9iamVjdCwgc28gd2UgbWlnaHQgc2VlXG4gICAgICAvLyBleHRyYSBwcm9wZXJ0aWVzIHdoaWNoIHdlcmVuJ3QgcmVhbGx5IHRoZXJlLiBBY2Nlc3NvciBwcm9wZXJ0aWVzIGhhdmVcbiAgICAgIC8vICdnZXQvc2V0L2VudW1lcmFibGUvY29uZmlndXJhYmxlJywgd2hpbGUgZGF0YSBwcm9wZXJ0aWVzIGhhdmVcbiAgICAgIC8vICd2YWx1ZS93cml0YWJsZS9lbnVtZXJhYmxlL2NvbmZpZ3VyYWJsZScuXG4gICAgICBkZXNjLmNvbmZpZ3VyYWJsZSA9PT0gZmFsc2UgJiZcbiAgICAgIGRlc2Mud3JpdGFibGUgPT09IGZhbHNlICYmXG4gICAgICAvL1xuICAgICAgLy8gQ2hlY2tzIGZvciBkYXRhIHByb3BlcnRpZXMgYmVjYXVzZSB0aGV5J3JlIHRoZSBvbmx5IG9uZXMgd2UgY2FuXG4gICAgICAvLyBvcHRpbWl6ZSAoYWNjZXNzb3JzIGFyZSBtb3N0IGxpa2VseSBub24tY29uc3RhbnQpLiBEZXNjcmlwdG9ycyBjYW4ndFxuICAgICAgLy8gY2FuJ3QgaGF2ZSBhY2Nlc3NvcnMgYW5kIHZhbHVlIHByb3BlcnRpZXMgYXQgdGhlIHNhbWUgdGltZSwgdGhlcmVmb3JlXG4gICAgICAvLyB0aGlzIGNoZWNrIGlzIHN1ZmZpY2llbnQuIFVzaW5nIGV4cGxpY2l0IG93biBwcm9wZXJ0eSBkZWFsIHdpdGggdGhlXG4gICAgICAvLyBjYXNlIHdoZXJlIE9iamVjdC5wcm90b3R5cGUgaGFzIGJlZW4gcG9pc29uZWQuXG4gICAgICBvYmplY3RIYXNPd25Qcm9wZXJ0eShkZXNjLCAndmFsdWUnKVxuICAgICk7XG4gIH1cblxuICAvKipcbiAgICogZ2V0U2NvcGVDb25zdGFudHMoKVxuICAgKiBXaGF0IHZhcmlhYmxlIG5hbWVzIG1pZ2h0IGl0IGJyaW5nIGludG8gc2NvcGU/IFRoZXNlIGluY2x1ZGUgYWxsXG4gICAqIHByb3BlcnR5IG5hbWVzIHdoaWNoIGNhbiBiZSB2YXJpYWJsZSBuYW1lcywgaW5jbHVkaW5nIHRoZSBuYW1lc1xuICAgKiBvZiBpbmhlcml0ZWQgcHJvcGVydGllcy4gSXQgZXhjbHVkZXMgc3ltYm9scyBhbmQgbmFtZXMgd2hpY2ggYXJlXG4gICAqIGtleXdvcmRzLiBXZSBkcm9wIHN5bWJvbHMgc2FmZWx5LiBDdXJyZW50bHksIHRoaXMgc2hpbSByZWZ1c2VzXG4gICAqIHNlcnZpY2UgaWYgYW55IG9mIHRoZSBuYW1lcyBhcmUga2V5d29yZHMgb3Iga2V5d29yZC1saWtlLiBUaGlzIGlzXG4gICAqIHNhZmUgYW5kIG9ubHkgcHJldmVudCBwZXJmb3JtYW5jZSBvcHRpbWl6YXRpb24uXG4gICAqXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBnbG9iYWxPYmplY3RcbiAgICogQHBhcmFtIHtPYmplY3R9IGxvY2FsT2JqZWN0XG4gICAqL1xuICBmdW5jdGlvbiBnZXRTY29wZUNvbnN0YW50cyhnbG9iYWxPYmplY3QsIGxvY2FsT2JqZWN0ID0ge30pIHtcbiAgICAvLyBnZXRPd25Qcm9wZXJ0eU5hbWVzKCkgZG9lcyBpZ25vcmUgU3ltYm9scyBzbyB3ZSBkb24ndCBuZWVkIHRvXG4gICAgLy8gZmlsdGVyIHRoZW0gb3V0LlxuICAgIGNvbnN0IGdsb2JhbE5hbWVzID0gZ2V0T3duUHJvcGVydHlOYW1lcyhnbG9iYWxPYmplY3QpO1xuICAgIGNvbnN0IGxvY2FsTmFtZXMgPSBnZXRPd25Qcm9wZXJ0eU5hbWVzKGxvY2FsT2JqZWN0KTtcblxuICAgIC8vIENvbGxlY3QgYWxsIHZhbGlkICYgaW1tdXRhYmxlIGlkZW50aWZpZXJzIGZyb20gdGhlIGVuZG93bWVudHMuXG4gICAgY29uc3QgbG9jYWxDb25zdGFudHMgPSBsb2NhbE5hbWVzLmZpbHRlcihcbiAgICAgIG5hbWUgPT5cbiAgICAgICAgaXNWYWxpZElkZW50aWZpZXJOYW1lKG5hbWUpICYmIGlzSW1tdXRhYmxlRGF0YVByb3BlcnR5KGxvY2FsT2JqZWN0LCBuYW1lKSxcbiAgICApO1xuXG4gICAgLy8gQ29sbGVjdCBhbGwgdmFsaWQgJiBpbW11dGFibGUgaWRlbnRpZmllcnMgZnJvbSB0aGUgZ2xvYmFsIHRoYXRcbiAgICAvLyBhcmUgYWxzbyBub3QgcHJlc2VudCBpbiB0aGUgZW5kd29tZW50cyAoaW1tdXRhYmxlIG9yIG5vdCkuXG4gICAgY29uc3QgZ2xvYmFsQ29uc3RhbnRzID0gZ2xvYmFsTmFtZXMuZmlsdGVyKFxuICAgICAgbmFtZSA9PlxuICAgICAgICAvLyBDYW4ndCBkZWZpbmUgYSBjb25zdGFudDogaXQgd291bGQgcHJldmVudCBhXG4gICAgICAgIC8vIGxvb2t1cCBvbiB0aGUgZW5kb3dtZW50cy5cbiAgICAgICAgIWxvY2FsTmFtZXMuaW5jbHVkZXMobmFtZSkgJiZcbiAgICAgICAgaXNWYWxpZElkZW50aWZpZXJOYW1lKG5hbWUpICYmXG4gICAgICAgIGlzSW1tdXRhYmxlRGF0YVByb3BlcnR5KGdsb2JhbE9iamVjdCwgbmFtZSksXG4gICAgKTtcblxuICAgIHJldHVybiBbLi4uZ2xvYmFsQ29uc3RhbnRzLCAuLi5sb2NhbENvbnN0YW50c107XG4gIH1cblxuICBjb25zdCB7IGRldGFpbHM6IGQkMSwgcXVvdGU6IHEkMSB9ID0gYXNzZXJ0O1xuXG4gIC8vIFRoZSBvcmlnaW5hbCB1bnNhZmUgdW50YW1lZCBldmFsIGZ1bmN0aW9uLCB3aGljaCBtdXN0IG5vdCBlc2NhcGUuXG4gIC8vIFNhbXBsZSBhdCBtb2R1bGUgaW5pdGlhbGl6YXRpb24gdGltZSwgd2hpY2ggaXMgYmVmb3JlIGxvY2tkb3duIGNhblxuICAvLyByZXBhaXIgaXQuICBVc2UgaXQgb25seSB0byBidWlsZCBwb3dlcmxlc3MgYWJzdHJhY3Rpb25zLlxuICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tZXZhbFxuICBjb25zdCBGRVJBTF9FVkFMID0gZXZhbDtcblxuICAvKipcbiAgICogYWx3YXlzVGhyb3dIYW5kbGVyXG4gICAqIFRoaXMgaXMgYW4gb2JqZWN0IHRoYXQgdGhyb3dzIGlmIGFueSBwcm9wZXJ5IGlzIGNhbGxlZC4gSXQncyB1c2VkIGFzXG4gICAqIGEgcHJveHkgaGFuZGxlciB3aGljaCB0aHJvd3Mgb24gYW55IHRyYXAgY2FsbGVkLlxuICAgKiBJdCdzIG1hZGUgZnJvbSBhIHByb3h5IHdpdGggYSBnZXQgdHJhcCB0aGF0IHRocm93cy4gSXQncyBzYWZlIHRvXG4gICAqIGNyZWF0ZSBvbmUgYW5kIHNoYXJlIGl0IGJldHdlZW4gYWxsIHNjb3BlSGFuZGxlcnMuXG4gICAqL1xuICBjb25zdCBhbHdheXNUaHJvd0hhbmRsZXIgPSBuZXcgUHJveHkoaW1tdXRhYmxlT2JqZWN0LCB7XG4gICAgZ2V0KF9zaGFkb3csIHByb3ApIHtcbiAgICAgIGFzc2VydC5mYWlsKFxuICAgICAgICBkJDFgUGxlYXNlIHJlcG9ydCB1bmV4cGVjdGVkIHNjb3BlIGhhbmRsZXIgdHJhcDogJHtxJDEoU3RyaW5nKHByb3ApKX1gLFxuICAgICAgKTtcbiAgICB9LFxuICB9KTtcblxuICAvKlxuICAgKiBjcmVhdGVTY29wZUhhbmRsZXIoKVxuICAgKiBTY29wZUhhbmRsZXIgbWFuYWdlcyBhIFByb3h5IHdoaWNoIHNlcnZlcyBhcyB0aGUgZ2xvYmFsIHNjb3BlIGZvciB0aGVcbiAgICogcGVyZm9ybUV2YWwgb3BlcmF0aW9uICh0aGUgUHJveHkgaXMgdGhlIGFyZ3VtZW50IG9mIGEgJ3dpdGgnIGJpbmRpbmcpLlxuICAgKiBBcyBkZXNjcmliZWQgaW4gY3JlYXRlU2FmZUV2YWx1YXRvcigpLCBpdCBoYXMgc2V2ZXJhbCBmdW5jdGlvbnM6XG4gICAqIC0gYWxsb3cgdGhlIHZlcnkgZmlyc3QgKGFuZCBvbmx5IHRoZSB2ZXJ5IGZpcnN0KSB1c2Ugb2YgJ2V2YWwnIHRvIG1hcCB0b1xuICAgKiB0aGUgcmVhbCAodW5zYWZlKSBldmFsIGZ1bmN0aW9uLCBzbyBpdCBhY3RzIGFzIGEgJ2RpcmVjdCBldmFsJyBhbmQgY2FuXG4gICAqIGFjY2VzcyBpdHMgbGV4aWNhbCBzY29wZSAod2hpY2ggbWFwcyB0byB0aGUgJ3dpdGgnIGJpbmRpbmcsIHdoaWNoIHRoZVxuICAgKiBTY29wZUhhbmRsZXIgYWxzbyBjb250cm9scykuXG4gICAqIC0gZW5zdXJlIHRoYXQgYWxsIHN1YnNlcXVlbnQgdXNlcyBvZiAnZXZhbCcgbWFwIHRvIHRoZSBzYWZlRXZhbHVhdG9yLFxuICAgKiB3aGljaCBsaXZlcyBhcyB0aGUgJ2V2YWwnIHByb3BlcnR5IG9mIHRoZSBzYWZlR2xvYmFsLlxuICAgKiAtIHJvdXRlIGFsbCBvdGhlciBwcm9wZXJ0eSBsb29rdXBzIGF0IHRoZSBzYWZlR2xvYmFsLlxuICAgKiAtIGhpZGUgdGhlIHVuc2FmZUdsb2JhbCB3aGljaCBsaXZlcyBvbiB0aGUgc2NvcGUgY2hhaW4gYWJvdmUgdGhlICd3aXRoJy5cbiAgICogLSBlbnN1cmUgdGhlIFByb3h5IGludmFyaWFudHMgZGVzcGl0ZSBzb21lIGdsb2JhbCBwcm9wZXJ0aWVzIGJlaW5nIGZyb3plbi5cbiAgICovXG4gIGZ1bmN0aW9uIGNyZWF0ZVNjb3BlSGFuZGxlcihcbiAgICBnbG9iYWxPYmplY3QsXG4gICAgbG9jYWxPYmplY3QgPSB7fSxcbiAgICB7IHNsb3BweUdsb2JhbHNNb2RlID0gZmFsc2UgfSA9IHt9LFxuICApIHtcbiAgICByZXR1cm4ge1xuICAgICAgLy8gVGhlIHNjb3BlIGhhbmRsZXIgdGhyb3dzIGlmIGFueSB0cmFwIG90aGVyIHRoYW4gZ2V0L3NldC9oYXMgYXJlIHJ1blxuICAgICAgLy8gKGUuZy4gZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9ycywgYXBwbHksIGdldFByb3RvdHlwZU9mKS5cbiAgICAgIF9fcHJvdG9fXzogYWx3YXlzVGhyb3dIYW5kbGVyLFxuXG4gICAgICAvLyBUaGlzIGZsYWcgYWxsb3cgdXMgdG8gZGV0ZXJtaW5lIGlmIHRoZSBldmFsKCkgY2FsbCBpcyBhbiBkb25lIGJ5IHRoZVxuICAgICAgLy8gcmVhbG0ncyBjb2RlIG9yIGlmIGl0IGlzIHVzZXItbGFuZCBpbnZvY2F0aW9uLCBzbyB3ZSBjYW4gcmVhY3QgZGlmZmVyZW50bHkuXG4gICAgICB1c2VVbnNhZmVFdmFsdWF0b3I6IGZhbHNlLFxuXG4gICAgICBnZXQoX3NoYWRvdywgcHJvcCkge1xuICAgICAgICBpZiAodHlwZW9mIHByb3AgPT09ICdzeW1ib2wnKSB7XG4gICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIFNwZWNpYWwgdHJlYXRtZW50IGZvciBldmFsLiBUaGUgdmVyeSBmaXJzdCBsb29rdXAgb2YgJ2V2YWwnIGdldHMgdGhlXG4gICAgICAgIC8vIHVuc2FmZSAocmVhbCBkaXJlY3QpIGV2YWwsIHNvIGl0IHdpbGwgZ2V0IHRoZSBsZXhpY2FsIHNjb3BlIHRoYXQgdXNlc1xuICAgICAgICAvLyB0aGUgJ3dpdGgnIGNvbnRleHQuXG4gICAgICAgIGlmIChwcm9wID09PSAnZXZhbCcpIHtcbiAgICAgICAgICAvLyB0ZXN0IHRoYXQgaXQgaXMgdHJ1ZSByYXRoZXIgdGhhbiBtZXJlbHkgdHJ1dGh5XG4gICAgICAgICAgaWYgKHRoaXMudXNlVW5zYWZlRXZhbHVhdG9yID09PSB0cnVlKSB7XG4gICAgICAgICAgICAvLyByZXZva2UgYmVmb3JlIHVzZVxuICAgICAgICAgICAgdGhpcy51c2VVbnNhZmVFdmFsdWF0b3IgPSBmYWxzZTtcbiAgICAgICAgICAgIHJldHVybiBGRVJBTF9FVkFMO1xuICAgICAgICAgIH1cbiAgICAgICAgICAvLyBmYWxsIHRocm91Z2hcbiAgICAgICAgfVxuXG4gICAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIGxvY2FsT2JqZWN0LlxuICAgICAgICBpZiAocHJvcCBpbiBsb2NhbE9iamVjdCkge1xuICAgICAgICAgIC8vIFVzZSByZWZsZWN0IHRvIGRlZmVhdCBhY2Nlc3NvcnMgdGhhdCBjb3VsZCBiZSBwcmVzZW50IG9uIHRoZVxuICAgICAgICAgIC8vIGxvY2FsT2JqZWN0IG9iamVjdCBpdHNlbGYgYXMgYHRoaXNgLlxuICAgICAgICAgIC8vIFRoaXMgaXMgZG9uZSBvdXQgb2YgYW4gb3ZlcmFidW5kYW5jZSBvZiBjYXV0aW9uLCBhcyB0aGUgU0VTIHNoaW1cbiAgICAgICAgICAvLyBvbmx5IHVzZSB0aGUgbG9jYWxPYmplY3QgY2FycnkgZ2xvYmFsTGV4aWNhbHMgYW5kIGxpdmUgYmluZGluZ1xuICAgICAgICAgIC8vIHRyYXBzLlxuICAgICAgICAgIC8vIFRoZSBnbG9iYWxMZXhpY2FscyBhcmUgY2FwdHVyZWQgYXMgYSBzbmFwc2hvdCBvZiB3aGF0J3MgcGFzc2VkIHRvXG4gICAgICAgICAgLy8gdGhlIENvbXBhcnRtZW50IGNvbnN0cnVjdG9yLCB3aGVyZWluIGFsbCBhY2Nlc3NvcnMgYW5kIHNldHRlcnMgYXJlXG4gICAgICAgICAgLy8gZWxpbWluYXRlZCBhbmQgdGhlIHJlc3VsdCBmcm96ZW4uXG4gICAgICAgICAgLy8gVGhlIGxpdmUgYmluZGluZyB0cmFwcyBkbyB1c2UgYWNjZXNzb3JzLCBhbmQgbm9uZSBvZiB0aG9zZSBhY2Nlc3NvcnNcbiAgICAgICAgICAvLyBtYWtlIHVzZSBvZiB0aGVpciByZWNlaXZlci5cbiAgICAgICAgICAvLyBMaXZlIGJpbmRpbmcgdHJhcHMgcHJvdmlkZSBubyBhdmVudWUgZm9yIHVzZXIgY29kZSB0byBvYnNlcnZlIHRoZVxuICAgICAgICAgIC8vIHJlY2VpdmVyLlxuICAgICAgICAgIHJldHVybiByZWZsZWN0R2V0KGxvY2FsT2JqZWN0LCBwcm9wLCBnbG9iYWxPYmplY3QpO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgZ2xvYmFsLlxuICAgICAgICByZXR1cm4gcmVmbGVjdEdldChnbG9iYWxPYmplY3QsIHByb3ApO1xuICAgICAgfSxcblxuICAgICAgc2V0KF9zaGFkb3csIHByb3AsIHZhbHVlKSB7XG4gICAgICAgIC8vIFByb3BlcnRpZXMgb2YgdGhlIGxvY2FsT2JqZWN0LlxuICAgICAgICBpZiAocHJvcCBpbiBsb2NhbE9iamVjdCkge1xuICAgICAgICAgIGNvbnN0IGRlc2MgPSBnZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IobG9jYWxPYmplY3QsIHByb3ApO1xuICAgICAgICAgIGlmICgndmFsdWUnIGluIGRlc2MpIHtcbiAgICAgICAgICAgIC8vIFdvcmsgYXJvdW5kIGEgcGVjdWxpYXIgYmVoYXZpb3IgaW4gdGhlIHNwZWNzLCB3aGVyZVxuICAgICAgICAgICAgLy8gdmFsdWUgcHJvcGVydGllcyBhcmUgZGVmaW5lZCBvbiB0aGUgcmVjZWl2ZXIuXG4gICAgICAgICAgICByZXR1cm4gcmVmbGVjdFNldChsb2NhbE9iamVjdCwgcHJvcCwgdmFsdWUpO1xuICAgICAgICAgIH1cbiAgICAgICAgICAvLyBFbnN1cmUgdGhhdCB0aGUgJ3RoaXMnIHZhbHVlIG9uIHNldHRlcnMgcmVzb2x2ZXNcbiAgICAgICAgICAvLyB0byB0aGUgc2FmZUdsb2JhbCwgbm90IHRvIHRoZSBsb2NhbE9iamVjdCBvYmplY3QuXG4gICAgICAgICAgcmV0dXJuIHJlZmxlY3RTZXQobG9jYWxPYmplY3QsIHByb3AsIHZhbHVlLCBnbG9iYWxPYmplY3QpO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gUHJvcGVydGllcyBvZiB0aGUgZ2xvYmFsLlxuICAgICAgICByZXR1cm4gcmVmbGVjdFNldChnbG9iYWxPYmplY3QsIHByb3AsIHZhbHVlKTtcbiAgICAgIH0sXG5cbiAgICAgIC8vIHdlIG5lZWQgaGFzKCkgdG8gcmV0dXJuIGZhbHNlIGZvciBzb21lIG5hbWVzIHRvIHByZXZlbnQgdGhlIGxvb2t1cCBmcm9tXG4gICAgICAvLyBjbGltYmluZyB0aGUgc2NvcGUgY2hhaW4gYW5kIGV2ZW50dWFsbHkgcmVhY2hpbmcgdGhlIHVuc2FmZUdsb2JhbFxuICAgICAgLy8gb2JqZWN0IChnbG9iYWxUaGlzKSwgd2hpY2ggaXMgYmFkLlxuXG4gICAgICAvLyB0b2RvOiB3ZSdkIGxpa2UgdG8ganVzdCBoYXZlIGhhcygpIHJldHVybiB0cnVlIGZvciBldmVyeXRoaW5nLCBhbmQgdGhlblxuICAgICAgLy8gdXNlIGdldCgpIHRvIHJhaXNlIGEgUmVmZXJlbmNlRXJyb3IgZm9yIGFueXRoaW5nIG5vdCBvbiB0aGUgc2FmZSBnbG9iYWwuXG4gICAgICAvLyBCdXQgd2Ugd2FudCB0byBiZSBjb21wYXRpYmxlIHdpdGggUmVmZXJlbmNlRXJyb3IgaW4gdGhlIG5vcm1hbCBjYXNlIGFuZFxuICAgICAgLy8gdGhlIGxhY2sgb2YgUmVmZXJlbmNlRXJyb3IgaW4gdGhlICd0eXBlb2YnIGNhc2UuIE11c3QgZWl0aGVyIHJlbGlhYmx5XG4gICAgICAvLyBkaXN0aW5ndWlzaCB0aGVzZSB0d28gY2FzZXMgKHRoZSB0cmFwIGJlaGF2aW9yIG1pZ2h0IGJlIGRpZmZlcmVudCksIG9yXG4gICAgICAvLyB3ZSByZWx5IG9uIGEgbWFuZGF0b3J5IHNvdXJjZS10by1zb3VyY2UgdHJhbnNmb3JtIHRvIGNoYW5nZSAndHlwZW9mIGFiYydcbiAgICAgIC8vIHRvIFhYWC4gV2UgYWxyZWFkeSBuZWVkIGEgbWFuZGF0b3J5IHBhcnNlIHRvIHByZXZlbnQgdGhlICdpbXBvcnQnLFxuICAgICAgLy8gc2luY2UgaXQncyBhIHNwZWNpYWwgZm9ybSBpbnN0ZWFkIG9mIG1lcmVseSBiZWluZyBhIGdsb2JhbCB2YXJpYWJsZS9cblxuICAgICAgLy8gbm90ZTogaWYgd2UgbWFrZSBoYXMoKSByZXR1cm4gdHJ1ZSBhbHdheXMsIHRoZW4gd2UgbXVzdCBpbXBsZW1lbnQgYVxuICAgICAgLy8gc2V0KCkgdHJhcCB0byBhdm9pZCBzdWJ2ZXJ0aW5nIHRoZSBwcm90ZWN0aW9uIG9mIHN0cmljdCBtb2RlIChpdCB3b3VsZFxuICAgICAgLy8gYWNjZXB0IGFzc2lnbm1lbnRzIHRvIHVuZGVmaW5lZCBnbG9iYWxzLCB3aGVuIGl0IG91Z2h0IHRvIHRocm93XG4gICAgICAvLyBSZWZlcmVuY2VFcnJvciBmb3Igc3VjaCBhc3NpZ25tZW50cylcblxuICAgICAgaGFzKF9zaGFkb3csIHByb3ApIHtcbiAgICAgICAgLy8gdW5zYWZlR2xvYmFsOiBoaWRlIGFsbCBwcm9wZXJ0aWVzIG9mIHRoZSBjdXJyZW50IGdsb2JhbFxuICAgICAgICAvLyBhdCB0aGUgZXhwZW5zZSBvZiAndHlwZW9mJyBiZWluZyB3cm9uZyBmb3IgdGhvc2UgcHJvcGVydGllcy4gRm9yXG4gICAgICAgIC8vIGV4YW1wbGUsIGluIHRoZSBicm93c2VyLCBldmFsdWF0aW5nICdkb2N1bWVudCA9IDMnLCB3aWxsIGFkZFxuICAgICAgICAvLyBhIHByb3BlcnR5IHRvIGdsb2JhbE9iamVjdCBpbnN0ZWFkIG9mIHRocm93aW5nIGEgUmVmZXJlbmNlRXJyb3IuXG4gICAgICAgIGlmIChcbiAgICAgICAgICBzbG9wcHlHbG9iYWxzTW9kZSB8fFxuICAgICAgICAgIHByb3AgPT09ICdldmFsJyB8fFxuICAgICAgICAgIHByb3AgaW4gbG9jYWxPYmplY3QgfHxcbiAgICAgICAgICBwcm9wIGluIGdsb2JhbE9iamVjdCB8fFxuICAgICAgICAgIHByb3AgaW4gZ2xvYmFsVGhpc1xuICAgICAgICApIHtcbiAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfVxuXG4gICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgIH0sXG5cbiAgICAgIC8vIG5vdGU6IHRoaXMgaXMgbGlrZWx5IGEgYnVnIG9mIHNhZmFyaVxuICAgICAgLy8gaHR0cHM6Ly9idWdzLndlYmtpdC5vcmcvc2hvd19idWcuY2dpP2lkPTE5NTUzNFxuXG4gICAgICBnZXRQcm90b3R5cGVPZigpIHtcbiAgICAgICAgcmV0dXJuIG51bGw7XG4gICAgICB9LFxuXG4gICAgICAvLyBDaGlwIGhhcyBzZWVuIHRoaXMgaGFwcGVuIHNpbmdsZSBzdGVwcGluZyB1bmRlciB0aGUgQ2hyb21lL3Y4IGRlYnVnZ2VyLlxuICAgICAgLy8gVE9ETyByZWNvcmQgaG93IHRvIHJlbGlhYmx5IHJlcHJvZHVjZSwgYW5kIHRvIHRlc3QgaWYgdGhpcyBmaXggaGVscHMuXG4gICAgICAvLyBUT0RPIHJlcG9ydCBhcyBidWcgdG8gdjggb3IgQ2hyb21lLCBhbmQgcmVjb3JkIGlzc3VlIGxpbmsgaGVyZS5cblxuICAgICAgZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKF90YXJnZXQsIHByb3ApIHtcbiAgICAgICAgLy8gQ29lcmNlIHdpdGggYFN0cmluZ2AgaW4gY2FzZSBwcm9wIGlzIGEgc3ltYm9sLlxuICAgICAgICBjb25zdCBxdW90ZWRQcm9wID0gSlNPTi5zdHJpbmdpZnkoU3RyaW5nKHByb3ApKTtcbiAgICAgICAgY29uc29sZS53YXJuKFxuICAgICAgICAgIGBnZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IgdHJhcCBvbiBzY29wZUhhbmRsZXIgZm9yICR7cXVvdGVkUHJvcH1gLFxuICAgICAgICAgIG5ldyBFcnJvcigpLnN0YWNrLFxuICAgICAgICApO1xuICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgfSxcbiAgICB9O1xuICB9XG5cbiAgLy8gQ2FwdHVyZXMgYSBrZXkgYW5kIHZhbHVlIG9mIHRoZSBmb3JtICNrZXk9dmFsdWUgb3IgQGtleT12YWx1ZVxuICBjb25zdCBzb3VyY2VNZXRhRW50cnlSZWdFeHAgPVxuICAgICdcXFxccypbQCNdXFxcXHMqKFthLXpBLVpdW2EtekEtWjAtOV0qKVxcXFxzKj1cXFxccyooW15cXFxcc1xcXFwqXSopJztcbiAgLy8gQ2FwdHVyZXMgZWl0aGVyIGEgb25lLWxpbmUgb3IgbXVsdGktbGluZSBjb21tZW50IGNvbnRhaW5pbmdcbiAgLy8gb25lICNrZXk9dmFsdWUgb3IgQGtleT12YWx1ZS5cbiAgLy8gUHJvZHVjZXMgdHdvIHBhaXJzIG9mIGNhcHR1cmUgZ3JvdXBzLCBidXQgdGhlIGluaXRpYWwgdHdvIG1heSBiZSB1bmRlZmluZWQuXG4gIC8vIE9uIGFjY291bnQgb2YgdGhlIG1lY2hhbmljcyBvZiByZWd1bGFyIGV4cHJlc3Npb25zLCBzY2FubmluZyBmcm9tIHRoZSBlbmRcbiAgLy8gZG9lcyBub3QgYWxsb3cgdXMgdG8gY2FwdHVyZSBldmVyeSBwYWlyLCBzbyBnZXRTb3VyY2VVUkwgbXVzdCBjYXB0dXJlIGFuZFxuICAvLyB0cmltIHVudGlsIHRoZXJlIGFyZSBubyBtYXRjaGluZyBjb21tZW50cy5cbiAgY29uc3Qgc291cmNlTWV0YUVudHJpZXNSZWdFeHAgPSBuZXcgUmVnRXhwKFxuICAgIGAoPzpcXFxccyovLyR7c291cmNlTWV0YUVudHJ5UmVnRXhwfXwvXFxcXCoke3NvdXJjZU1ldGFFbnRyeVJlZ0V4cH1cXFxccypcXFxcKi8pXFxcXHMqJGAsXG4gICk7XG5cbiAgZnVuY3Rpb24gZ2V0U291cmNlVVJMKHNyYykge1xuICAgIGxldCBzb3VyY2VVUkwgPSAnPHVua25vd24+JztcblxuICAgIC8vIE91ciByZWd1bGFyIGV4cHJlc3Npb24gbWF0Y2hlcyB0aGUgbGFzdCBvbmUgb3IgdHdvIGNvbW1lbnRzIHdpdGgga2V5IHZhbHVlXG4gICAgLy8gcGFpcnMgYXQgdGhlIGVuZCBvZiB0aGUgc291cmNlLCBhdm9pZGluZyBhIHNjYW4gb3ZlciB0aGUgZW50aXJlIGxlbmd0aCBvZlxuICAgIC8vIHRoZSBzdHJpbmcsIGJ1dCBhdCB0aGUgZXhwZW5zZSBvZiBiZWluZyBhYmxlIHRvIGNhcHR1cmUgYWxsIHRoZSAoa2V5LFxuICAgIC8vIHZhbHVlKSBwYWlyIG1ldGEgY29tbWVudHMgYXQgdGhlIGVuZCBvZiB0aGUgc291cmNlLCB3aGljaCBtYXkgaW5jbHVkZVxuICAgIC8vIHNvdXJjZU1hcFVSTCBpbiBhZGRpdGlvbiB0byBzb3VyY2VVUkwuXG4gICAgLy8gU28sIHdlIHN1YmxpbWF0ZSB0aGUgY29tbWVudHMgb3V0IG9mIHRoZSBzb3VyY2UgdW50aWwgbm8gc291cmNlIG9yIG5vXG4gICAgLy8gY29tbWVudHMgcmVtYWluLlxuICAgIHdoaWxlIChzcmMubGVuZ3RoID4gMCkge1xuICAgICAgY29uc3QgbWF0Y2ggPSBzb3VyY2VNZXRhRW50cmllc1JlZ0V4cC5leGVjKHNyYyk7XG4gICAgICBpZiAobWF0Y2ggPT09IG51bGwpIHtcbiAgICAgICAgYnJlYWs7XG4gICAgICB9XG4gICAgICBzcmMgPSBzcmMuc2xpY2UoMCwgc3JjLmxlbmd0aCAtIG1hdGNoWzBdLmxlbmd0aCk7XG5cbiAgICAgIC8vIFdlIHNraXAgJDAgc2luY2UgaXQgY29udGFpbnMgdGhlIGVudGlyZSBtYXRjaC5cbiAgICAgIC8vIFRoZSBtYXRjaCBjb250YWlucyBmb3VyIGNhcHR1cmUgZ3JvdXBzLFxuICAgICAgLy8gdHdvIChrZXksIHZhbHVlKSBwYWlycywgdGhlIGZpcnN0IG9mIHdoaWNoXG4gICAgICAvLyBtYXkgYmUgdW5kZWZpbmVkLlxuICAgICAgLy8gT24gdGhlIG9mZi1jaGFuY2Ugc29tZW9uZSBwdXQgdHdvIHNvdXJjZVVSTCBjb21tZW50cyBpbiB0aGVpciBjb2RlIHdpdGhcbiAgICAgIC8vIGRpZmZlcmVudCBjb21tZW50aW5nIGNvbnZlbnRpb25zLCB0aGUgbGF0dGVyIGhhcyBwcmVjZWRlbmNlLlxuICAgICAgaWYgKG1hdGNoWzNdID09PSAnc291cmNlVVJMJykge1xuICAgICAgICBzb3VyY2VVUkwgPSBtYXRjaFs0XTtcbiAgICAgIH0gZWxzZSBpZiAobWF0Y2hbMV0gPT09ICdzb3VyY2VVUkwnKSB7XG4gICAgICAgIHNvdXJjZVVSTCA9IG1hdGNoWzJdO1xuICAgICAgfVxuICAgIH1cblxuICAgIHJldHVybiBzb3VyY2VVUkw7XG4gIH1cblxuICAvLyBAdHMtY2hlY2tcblxuICAvKipcbiAgICogRmluZCB0aGUgZmlyc3Qgb2NjdXJlbmNlIG9mIHRoZSBnaXZlbiBwYXR0ZXJuIGFuZCByZXR1cm5cbiAgICogdGhlIGxvY2F0aW9uIGFzIHRoZSBhcHByb3hpbWF0ZSBsaW5lIG51bWJlci5cbiAgICpcbiAgICogQHBhcmFtIHtzdHJpbmd9IHNyY1xuICAgKiBAcGFyYW0ge1JlZ0V4cH0gcGF0dGVyblxuICAgKiBAcmV0dXJucyB7bnVtYmVyfVxuICAgKi9cbiAgZnVuY3Rpb24gZ2V0TGluZU51bWJlcihzcmMsIHBhdHRlcm4pIHtcbiAgICBjb25zdCBpbmRleCA9IHN0cmluZ1NlYXJjaChzcmMsIHBhdHRlcm4pO1xuICAgIGlmIChpbmRleCA8IDApIHtcbiAgICAgIHJldHVybiAtMTtcbiAgICB9XG4gICAgcmV0dXJuIHN0cmluZ1NwbGl0KHN0cmluZ1NsaWNlKHNyYywgMCwgaW5kZXgpLCAnXFxuJykubGVuZ3RoO1xuICB9XG5cbiAgLy8gLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy9cblxuICBjb25zdCBodG1sQ29tbWVudFBhdHRlcm4gPSBuZXcgUmVnRXhwKGAoPzokeyc8J30hLS18LS0keyc+J30pYCwgJ2cnKTtcblxuICAvKipcbiAgICogQ29uc2VydmF0aXZlbHkgcmVqZWN0IHRoZSBzb3VyY2UgdGV4dCBpZiBpdCBtYXkgY29udGFpbiB0ZXh0IHRoYXQgc29tZVxuICAgKiBKYXZhU2NyaXB0IHBhcnNlcnMgbWF5IHRyZWF0IGFzIGFuIGh0bWwtbGlrZSBjb21tZW50LiBUbyByZWplY3Qgd2l0aG91dFxuICAgKiBwYXJzaW5nLCBgcmVqZWN0SHRtbENvbW1lbnRzYCB3aWxsIGFsc28gcmVqZWN0IHNvbWUgb3RoZXIgdGV4dCBhcyB3ZWxsLlxuICAgKlxuICAgKiBodHRwczovL3d3dy5lY21hLWludGVybmF0aW9uYWwub3JnL2VjbWEtMjYyLzkuMC9pbmRleC5odG1sI3NlYy1odG1sLWxpa2UtY29tbWVudHNcbiAgICogZXhwbGFpbnMgdGhhdCBKYXZhU2NyaXB0IHBhcnNlcnMgbWF5IG9yIG1heSBub3QgcmVjb2duaXplIGh0bWxcbiAgICogY29tbWVudCB0b2tlbnMgXCI8XCIgaW1tZWRpYXRlbHkgZm9sbG93ZWQgYnkgXCIhLS1cIiBhbmQgXCItLVwiXG4gICAqIGltbWVkaWF0ZWx5IGZvbGxvd2VkIGJ5IFwiPlwiIGluIG5vbi1tb2R1bGUgc291cmNlIHRleHQsIGFuZCB0cmVhdFxuICAgKiB0aGVtIGFzIGEga2luZCBvZiBsaW5lIGNvbW1lbnQuIFNpbmNlIG90aGVyd2lzZSBib3RoIG9mIHRoZXNlIGNhblxuICAgKiBhcHBlYXIgaW4gbm9ybWFsIEphdmFTY3JpcHQgc291cmNlIGNvZGUgYXMgYSBzZXF1ZW5jZSBvZiBvcGVyYXRvcnMsXG4gICAqIHdlIGhhdmUgdGhlIHRlcnJpZnlpbmcgcG9zc2liaWxpdHkgb2YgdGhlIHNhbWUgc291cmNlIGNvZGUgcGFyc2luZ1xuICAgKiBvbmUgd2F5IG9uIG9uZSBjb3JyZWN0IEphdmFTY3JpcHQgaW1wbGVtZW50YXRpb24sIGFuZCBhbm90aGVyIHdheVxuICAgKiBvbiBhbm90aGVyLlxuICAgKlxuICAgKiBUaGlzIHNoaW0gdGFrZXMgdGhlIGNvbnNlcnZhdGl2ZSBzdHJhdGVneSBvZiBqdXN0IHJlamVjdGluZyBzb3VyY2VcbiAgICogdGV4dCB0aGF0IGNvbnRhaW5zIHRoZXNlIHN0cmluZ3MgYW55d2hlcmUuIE5vdGUgdGhhdCB0aGlzIHZlcnlcbiAgICogc291cmNlIGZpbGUgaXMgd3JpdHRlbiBzdHJhbmdlbHkgdG8gYXZvaWQgbWVudGlvbmluZyB0aGVzZVxuICAgKiBjaGFyYWN0ZXIgc3RyaW5ncyBleHBsaWNpdGx5LlxuICAgKlxuICAgKiBXZSBkbyBub3Qgd3JpdGUgdGhlIHJlZ2V4cCBpbiBhIHN0cmFpZ2h0Zm9yd2FyZCB3YXksIHNvIHRoYXQgYW5cbiAgICogYXBwYXJlbm50IGh0bWwgY29tbWVudCBkb2VzIG5vdCBhcHBlYXIgaW4gdGhpcyBmaWxlLiBUaHVzLCB3ZSBhdm9pZFxuICAgKiByZWplY3Rpb24gYnkgdGhlIG92ZXJseSBlYWdlciByZWplY3REYW5nZXJvdXNTb3VyY2VzLlxuICAgKlxuICAgKiBAcGFyYW0ge3N0cmluZ30gc3JjXG4gICAqIEByZXR1cm5zIHtzdHJpbmd9XG4gICAqL1xuICBmdW5jdGlvbiByZWplY3RIdG1sQ29tbWVudHMoc3JjKSB7XG4gICAgY29uc3QgbGluZU51bWJlciA9IGdldExpbmVOdW1iZXIoc3JjLCBodG1sQ29tbWVudFBhdHRlcm4pO1xuICAgIGlmIChsaW5lTnVtYmVyIDwgMCkge1xuICAgICAgcmV0dXJuIHNyYztcbiAgICB9XG4gICAgY29uc3QgbmFtZSA9IGdldFNvdXJjZVVSTChzcmMpO1xuICAgIHRocm93IG5ldyBTeW50YXhFcnJvcihcbiAgICAgIGBQb3NzaWJsZSBIVE1MIGNvbW1lbnQgcmVqZWN0ZWQgYXQgJHtuYW1lfToke2xpbmVOdW1iZXJ9LiAoU0VTX0hUTUxfQ09NTUVOVF9SRUpFQ1RFRClgLFxuICAgICk7XG4gIH1cblxuICAvKipcbiAgICogQW4gb3B0aW9uYWwgdHJhbnNmb3JtIHRvIHBsYWNlIGFoZWFkIG9mIGByZWplY3RIdG1sQ29tbWVudHNgIHRvIGV2YWRlICp0aGF0KlxuICAgKiByZWplY3Rpb24uIEhvd2V2ZXIsIGl0IG1heSBjaGFuZ2UgdGhlIG1lYW5pbmcgb2YgdGhlIHByb2dyYW0uXG4gICAqXG4gICAqIFRoaXMgZXZhc2lvbiByZXBsYWNlcyBlYWNoIGFsbGVnZWQgaHRtbCBjb21tZW50IHdpdGggdGhlIHNwYWNlLXNlcGFyYXRlZFxuICAgKiBKYXZhU2NyaXB0IG9wZXJhdG9yIHNlcXVlbmNlIHRoYXQgaXQgbWF5IG1lYW4sIGFzc3VtaW5nIHRoYXQgaXQgYXBwZWFyc1xuICAgKiBvdXRzaWRlIG9mIGEgY29tbWVudCBvciBsaXRlcmFsIHN0cmluZywgaW4gc291cmNlIGNvZGUgd2hlcmUgdGhlIEpTXG4gICAqIHBhcnNlciBtYWtlcyBubyBzcGVjaWFsIGNhc2UgZm9yIGh0bWwgY29tbWVudHMgKGxpa2UgbW9kdWxlIHNvdXJjZSBjb2RlKS5cbiAgICogSW4gdGhhdCBjYXNlLCB0aGlzIGV2YXNpb24gcHJlc2VydmVzIHRoZSBtZWFuaW5nIG9mIHRoZSBwcm9ncmFtLCB0aG91Z2ggaXRcbiAgICogZG9lcyBjaGFuZ2UgdGhlIHNvdWNlIGNvbHVtbiBudW1iZXJzIG9uIGVhY2ggZWZmZWN0ZWQgbGluZS5cbiAgICpcbiAgICogSWYgdGhlIGh0bWwgY29tbWVudCBhcHBlYXJlZCBpbiBhIGxpdGVyYWwgKGEgc3RyaW5nIGxpdGVyYWwsIHJlZ2V4cCBsaXRlcmFsLFxuICAgKiBvciBhIHRlbXBsYXRlIGxpdGVyYWwpLCB0aGVuIHRoaXMgZXZhc2lvbiB3aWxsIGNoYW5nZSB0aGUgbWVhbmluZyBvZiB0aGVcbiAgICogcHJvZ3JhbSBieSBjaGFuZ2luZyB0aGUgdGV4dCBvZiB0aGF0IGxpdGVyYWwuXG4gICAqXG4gICAqIElmIHRoZSBodG1sIGNvbW1lbnQgYXBwZWFyZWQgaW4gYSBKYXZhU2NyaXB0IGNvbW1lbnQsIHRoZW4gdGhpcyBldmFzaW9uIGRvZXNcbiAgICogbm90IGNoYW5nZSB0aGUgbWVhbmluZyBvZiB0aGUgcHJvZ3JhbSBiZWNhdXNlIGl0IG9ubHkgY2hhbmdlcyB0aGUgY29udGVudHMgb2ZcbiAgICogdGhvc2UgY29tbWVudHMuXG4gICAqXG4gICAqIEBwYXJhbSB7IHN0cmluZyB9IHNyY1xuICAgKiBAcmV0dXJucyB7IHN0cmluZyB9XG4gICAqL1xuICBmdW5jdGlvbiBldmFkZUh0bWxDb21tZW50VGVzdChzcmMpIHtcbiAgICBjb25zdCByZXBsYWNlRm4gPSBtYXRjaCA9PiAobWF0Y2hbMF0gPT09ICc8JyA/ICc8ICEgLS0nIDogJy0tID4nKTtcbiAgICByZXR1cm4gc3JjLnJlcGxhY2UoaHRtbENvbW1lbnRQYXR0ZXJuLCByZXBsYWNlRm4pO1xuICB9XG5cbiAgLy8gLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy9cblxuICBjb25zdCBpbXBvcnRQYXR0ZXJuID0gbmV3IFJlZ0V4cCgnXFxcXGJpbXBvcnQoXFxcXHMqKD86XFxcXCh8L1svKl0pKScsICdnJyk7XG5cbiAgLyoqXG4gICAqIENvbnNlcnZhdGl2ZWx5IHJlamVjdCB0aGUgc291cmNlIHRleHQgaWYgaXQgbWF5IGNvbnRhaW4gYSBkeW5hbWljXG4gICAqIGltcG9ydCBleHByZXNzaW9uLiBUbyByZWplY3Qgd2l0aG91dCBwYXJzaW5nLCBgcmVqZWN0SW1wb3J0RXhwcmVzc2lvbnNgIHdpbGxcbiAgICogYWxzbyByZWplY3Qgc29tZSBvdGhlciB0ZXh0IGFzIHdlbGwuXG4gICAqXG4gICAqIFRoZSBwcm9wb3NlZCBkeW5hbWljIGltcG9ydCBleHByZXNzaW9uIGlzIHRoZSBvbmx5IHN5bnRheCBjdXJyZW50bHlcbiAgICogcHJvcG9zZWQsIHRoYXQgY2FuIGFwcGVhciBpbiBub24tbW9kdWxlIEphdmFTY3JpcHQgY29kZSwgdGhhdFxuICAgKiBlbmFibGVzIGRpcmVjdCBhY2Nlc3MgdG8gdGhlIG91dHNpZGUgd29ybGQgdGhhdCBjYW5ub3QgYmVcbiAgICogc3VycHJlc3NlZCBvciBpbnRlcmNlcHRlZCB3aXRob3V0IHBhcnNpbmcgYW5kIHJld3JpdGluZy4gSW5zdGVhZCxcbiAgICogdGhpcyBzaGltIGNvbnNlcnZhdGl2ZWx5IHJlamVjdHMgYW55IHNvdXJjZSB0ZXh0IHRoYXQgc2VlbXMgdG9cbiAgICogY29udGFpbiBzdWNoIGFuIGV4cHJlc3Npb24uIFRvIGRvIHRoaXMgc2FmZWx5IHdpdGhvdXQgcGFyc2luZywgd2VcbiAgICogbXVzdCBhbHNvIHJlamVjdCBzb21lIHZhbGlkIHByb2dyYW1zLCBpLmUuLCB0aG9zZSBjb250YWluaW5nXG4gICAqIGFwcGFyZW50IGltcG9ydCBleHByZXNzaW9ucyBpbiBsaXRlcmFsIHN0cmluZ3Mgb3IgY29tbWVudHMuXG4gICAqXG4gICAqIFRoZSBjdXJyZW50IGNvbnNlcnZhdGl2ZSBydWxlIGxvb2tzIGZvciB0aGUgaWRlbnRpZmllciBcImltcG9ydFwiXG4gICAqIGZvbGxvd2VkIGJ5IGVpdGhlciBhbiBvcGVuIHBhcmVuIG9yIHNvbWV0aGluZyB0aGF0IGxvb2tzIGxpa2UgdGhlXG4gICAqIGJlZ2lubmluZyBvZiBhIGNvbW1lbnQuIFdlIGFzc3VtZSB0aGF0IHdlIGRvIG5vdCBuZWVkIHRvIHdvcnJ5XG4gICAqIGFib3V0IGh0bWwgY29tbWVudCBzeW50YXggYmVjYXVzZSB0aGF0IHdhcyBhbHJlYWR5IHJlamVjdGVkIGJ5XG4gICAqIHJlamVjdEh0bWxDb21tZW50cy5cbiAgICpcbiAgICogdGhpcyBcXHMgKm11c3QqIG1hdGNoIGFsbCBraW5kcyBvZiBzeW50YXgtZGVmaW5lZCB3aGl0ZXNwYWNlLiBJZiBlLmcuXG4gICAqIFUrMjAyOCAoTElORSBTRVBBUkFUT1IpIG9yIFUrMjAyOSAoUEFSQUdSQVBIIFNFUEFSQVRPUikgaXMgdHJlYXRlZCBhc1xuICAgKiB3aGl0ZXNwYWNlIGJ5IHRoZSBwYXJzZXIsIGJ1dCBub3QgbWF0Y2hlZCBieSAvXFxzLywgdGhlbiB0aGlzIHdvdWxkIGFkbWl0XG4gICAqIGFuIGF0dGFjayBsaWtlOiBpbXBvcnRcXHUyMDI4KCdwb3dlci5qcycpIC4gV2UncmUgdHJ5aW5nIHRvIGRpc3Rpbmd1aXNoXG4gICAqIHNvbWV0aGluZyBsaWtlIHRoYXQgZnJvbSBzb21ldGhpbmcgbGlrZSBpbXBvcnRub3RyZWFsbHkoJ3Bvd2VyLmpzJykgd2hpY2hcbiAgICogaXMgcGVyZmVjdGx5IHNhZmUuXG4gICAqXG4gICAqIEBwYXJhbSB7IHN0cmluZyB9IHNyY1xuICAgKiBAcmV0dXJucyB7IHN0cmluZyB9XG4gICAqL1xuICBmdW5jdGlvbiByZWplY3RJbXBvcnRFeHByZXNzaW9ucyhzcmMpIHtcbiAgICBjb25zdCBsaW5lTnVtYmVyID0gZ2V0TGluZU51bWJlcihzcmMsIGltcG9ydFBhdHRlcm4pO1xuICAgIGlmIChsaW5lTnVtYmVyIDwgMCkge1xuICAgICAgcmV0dXJuIHNyYztcbiAgICB9XG4gICAgY29uc3QgbmFtZSA9IGdldFNvdXJjZVVSTChzcmMpO1xuICAgIHRocm93IG5ldyBTeW50YXhFcnJvcihcbiAgICAgIGBQb3NzaWJsZSBpbXBvcnQgZXhwcmVzc2lvbiByZWplY3RlZCBhdCAke25hbWV9OiR7bGluZU51bWJlcn0uIChTRVNfSU1QT1JUX1JFSkVDVEVEKWAsXG4gICAgKTtcbiAgfVxuXG4gIC8qKlxuICAgKiBBbiBvcHRpb25hbCB0cmFuc2Zvcm0gdG8gcGxhY2UgYWhlYWQgb2YgYHJlamVjdEltcG9ydEV4cHJlc3Npb25zYCB0byBldmFkZVxuICAgKiAqdGhhdCogcmVqZWN0aW9uLiBIb3dldmVyLCBpdCBtYXkgY2hhbmdlIHRoZSBtZWFuaW5nIG9mIHRoZSBwcm9ncmFtLlxuICAgKlxuICAgKiBUaGlzIGV2YXNpb24gcmVwbGFjZXMgZWFjaCBzdXNwaWNpb3VzIGBpbXBvcnRgIGlkZW50aWZpZXIgd2l0aCBgX19pbXBvcnRfX2AuXG4gICAqIElmIHRoZSBhbGxlZ2VkIGltcG9ydCBleHByZXNzaW9uIGFwcGVhcnMgaW4gYSBKYXZhU2NyaXB0IGNvbW1lbnQsIHRoaXNcbiAgICogZXZhc2lvbiB3aWxsIG5vdCBjaGFuZ2UgdGhlIG1lYW5pbmcgb2YgdGhlIHByb2dyYW0uIElmIGl0IGFwcGVhcnMgaW4gYVxuICAgKiBsaXRlcmFsIChzdHJpbmcgbGl0ZXJhbCwgcmVnZXhwIGxpdGVyYWwsIG9yIGEgdGVtcGxhdGUgbGl0ZXJhbCksIHRoZW4gdGhpc1xuICAgKiBldmFzaW9uIHdpbGwgY2hhbmdlIHRoZSBjb250ZW50cyBvZiB0aGF0IGxpdGVyYWwuIElmIGl0IGFwcGVhcnMgYXMgY29kZVxuICAgKiB3aGVyZSBpdCB3b3VsZCBiZSBwYXJzZWQgYXMgYW4gZXhwcmVzc2lvbiwgdGhlbiBpdCBtaWdodCBvciBtaWdodCBub3QgY2hhbmdlXG4gICAqIHRoZSBtZWFuaW5nIG9mIHRoZSBwcm9ncmFtLCBkZXBlbmRpbmcgb24gdGhlIGJpbmRpbmcsIGlmIGFueSwgb2YgdGhlIGxleGljYWxcbiAgICogdmFyaWFibGUgYF9faW1wb3J0X19gLlxuICAgKlxuICAgKiBGaW5hbGx5LCBpZiB0aGUgb3JpZ2luYWwgYXBwZWFycyBpbiBjb2RlIHdoZXJlIGl0IGlzIG5vdCBwYXJzZWQgYXMgYW5cbiAgICogZXhwcmVzc2lvbiwgZm9yIGV4YW1wbGUgYGZvby5pbXBvcnQocGF0aClgLCB0aGVuIHRoaXMgZXZhc2lvbiB3b3VsZCByZXdyaXRlXG4gICAqIHRvIGBmb28uX19pbXBvcnRfXyhwYXRoKWAgd2hpY2ggaGFzIGEgc3VycHJpc2luZ2x5IGRpZmZlcmVudCBtZWFuaW5nLlxuICAgKlxuICAgKiBAcGFyYW0geyBzdHJpbmcgfSBzcmNcbiAgICogQHJldHVybnMgeyBzdHJpbmcgfVxuICAgKi9cbiAgZnVuY3Rpb24gZXZhZGVJbXBvcnRFeHByZXNzaW9uVGVzdChzcmMpIHtcbiAgICBjb25zdCByZXBsYWNlRm4gPSAoXywgcDEpID0+IGBfX2ltcG9ydF9fJHtwMX1gO1xuICAgIHJldHVybiBzcmMucmVwbGFjZShpbXBvcnRQYXR0ZXJuLCByZXBsYWNlRm4pO1xuICB9XG5cbiAgLy8gLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy9cblxuICBjb25zdCBzb21lRGlyZWN0RXZhbFBhdHRlcm4gPSBuZXcgUmVnRXhwKCdcXFxcYmV2YWwoXFxcXHMqXFxcXCgpJywgJ2cnKTtcblxuICAvKipcbiAgICogSGV1cmlzdGljYWxseSByZWplY3Qgc29tZSB0ZXh0IHRoYXQgc2VlbXMgdG8gY29udGFpbiBhIGRpcmVjdCBldmFsXG4gICAqIGV4cHJlc3Npb24sIHdpdGggYm90aCBmYWxzZSBwb3NpdGl2ZXMgYW5kIGZhbHNlIG5lZ2F2aXZlcy4gVG8gcmVqZWN0IHdpdGhvdXRcbiAgICogcGFyc2luZywgYHJlamVjdFNvbWVEaXJlY3RFdmFsRXhwcmVzc2lvbnNgIG1heSB3aWxsIGFsc28gcmVqZWN0IHNvbWUgb3RoZXJcbiAgICogdGV4dCBhcyB3ZWxsLiBJdCBtYXkgYWxzbyBhY2NlcHQgc291cmNlIHRleHQgdGhhdCBjb250YWlucyBhIGRpcmVjdCBldmFsXG4gICAqIHdyaXR0ZW4gb2RkbHksIHN1Y2ggYXMgYChldmFsKShzcmMpYC4gVGhpcyBmYWxzZSBuZWdhdGl2ZSBpcyBub3QgYSBzZWN1cml0eVxuICAgKiB2dWxuZXJhYmlsaXR5LiBSYXRoZXIgaXQgaXMgYSBjb21wYXQgaGF6YXJkIGJlY2F1c2UgaXQgd2lsbCBleGVjdXRlIGFzXG4gICAqIGFuIGluZGlyZWN0IGV2YWwgdW5kZXIgdGhlIFNFUy1zaGltIGJ1dCBhcyBhIGRpcmVjdCBldmFsIG9uIHBsYXRmb3JtcyB0aGF0XG4gICAqIHN1cHBvcnQgU0VTIGRpcmVjdGx5IChsaWtlIFhTKS5cbiAgICpcbiAgICogVGhlIHNoaW0gY2Fubm90IGNvcnJlY3RseSBlbXVsYXRlIGEgZGlyZWN0IGV2YWwgYXMgZXhwbGFpbmVkIGF0XG4gICAqIGh0dHBzOi8vZ2l0aHViLmNvbS9BZ29yaWMvcmVhbG1zLXNoaW0vaXNzdWVzLzEyXG4gICAqIElmIHdlIGRpZCBub3QgcmVqZWN0IGRpcmVjdCBldmFsIHN5bnRheCwgd2Ugd291bGRcbiAgICogYWNjaWRlbnRhbGx5IGV2YWx1YXRlIHRoZXNlIHdpdGggYW4gZW11bGF0aW9uIG9mIGluZGlyZWN0IGV2YWwuIFRvXG4gICAqIHByZXZlbnQgZnV0dXJlIGNvbXBhdGliaWxpdHkgcHJvYmxlbXMsIGluIHNoaWZ0aW5nIGZyb20gdXNlIG9mIHRoZVxuICAgKiBzaGltIHRvIGdlbnVpbmUgcGxhdGZvcm0gc3VwcG9ydCBmb3IgdGhlIHByb3Bvc2FsLCB3ZSBzaG91bGRcbiAgICogaW5zdGVhZCBzdGF0aWNhbGx5IHJlamVjdCBjb2RlIHRoYXQgc2VlbXMgdG8gY29udGFpbiBhIGRpcmVjdCBldmFsXG4gICAqIGV4cHJlc3Npb24uXG4gICAqXG4gICAqIEFzIHdpdGggdGhlIGR5bmFtaWMgaW1wb3J0IGV4cHJlc3Npb24sIHRvIGF2b2lkIGEgZnVsbCBwYXJzZSwgd2UgZG9cbiAgICogdGhpcyBhcHByb3hpbWF0ZWx5IHdpdGggYSByZWdleHAsIHRoYXQgd2lsbCBhbHNvIHJlamVjdCBzdHJpbmdzXG4gICAqIHRoYXQgYXBwZWFyIHNhZmVseSBpbiBjb21tZW50cyBvciBzdHJpbmdzLiBVbmxpa2UgZHluYW1pYyBpbXBvcnQsXG4gICAqIGlmIHdlIG1pc3Mgc29tZSwgdGhpcyBvbmx5IGNyZWF0ZXMgZnV0dXJlIGNvbXBhdCBwcm9ibGVtcywgbm90XG4gICAqIHNlY3VyaXR5IHByb2JsZW1zLiBUaHVzLCB3ZSBhcmUgb25seSB0cnlpbmcgdG8gY2F0Y2ggaW5ub2NlbnRcbiAgICogb2NjdXJyZW5jZXMsIG5vdCBtYWxpY2lvdXMgb25lLiBJbiBwYXJ0aWN1bGFyLCBgKGV2YWwpKC4uLilgIGlzXG4gICAqIGRpcmVjdCBldmFsIHN5bnRheCB0aGF0IHdvdWxkIG5vdCBiZSBjYXVnaHQgYnkgdGhlIGZvbGxvd2luZyByZWdleHAuXG4gICAqXG4gICAqIEV4cG9ydGVkIGZvciB1bml0IHRlc3RzLlxuICAgKlxuICAgKiBAcGFyYW0geyBzdHJpbmcgfSBzcmNcbiAgICogQHJldHVybnMgeyBzdHJpbmcgfVxuICAgKi9cbiAgZnVuY3Rpb24gcmVqZWN0U29tZURpcmVjdEV2YWxFeHByZXNzaW9ucyhzcmMpIHtcbiAgICBjb25zdCBsaW5lTnVtYmVyID0gZ2V0TGluZU51bWJlcihzcmMsIHNvbWVEaXJlY3RFdmFsUGF0dGVybik7XG4gICAgaWYgKGxpbmVOdW1iZXIgPCAwKSB7XG4gICAgICByZXR1cm4gc3JjO1xuICAgIH1cbiAgICBjb25zdCBuYW1lID0gZ2V0U291cmNlVVJMKHNyYyk7XG4gICAgdGhyb3cgbmV3IFN5bnRheEVycm9yKFxuICAgICAgYFBvc3NpYmxlIGRpcmVjdCBldmFsIGV4cHJlc3Npb24gcmVqZWN0ZWQgYXQgJHtuYW1lfToke2xpbmVOdW1iZXJ9LiAoU0VTX0VWQUxfUkVKRUNURUQpYCxcbiAgICApO1xuICB9XG5cbiAgLy8gLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy9cblxuICAvKipcbiAgICogQSB0cmFuc2Zvcm0gdGhhdCBidW5kbGVzIHRvZ2V0aGVyIHRoZSB0cmFuc2Zvcm1zIHRoYXQgbXVzdCB1bmNvbmRpdGlvbmFsbHlcbiAgICogaGFwcGVuIGxhc3QgaW4gb3JkZXIgdG8gZW5zdXJlIHNhZmUgZXZhbHVhdGlvbiB3aXRob3V0IHBhcnNpbmcuXG4gICAqXG4gICAqIEBwYXJhbSB7c3RyaW5nfSBzb3VyY2VcbiAgICogQHJldHVybnMge3N0cmluZ31cbiAgICovXG4gIGZ1bmN0aW9uIG1hbmRhdG9yeVRyYW5zZm9ybXMoc291cmNlKSB7XG4gICAgc291cmNlID0gcmVqZWN0SHRtbENvbW1lbnRzKHNvdXJjZSk7XG4gICAgc291cmNlID0gcmVqZWN0SW1wb3J0RXhwcmVzc2lvbnMoc291cmNlKTtcbiAgICByZXR1cm4gc291cmNlO1xuICB9XG5cbiAgLyoqXG4gICAqIFN0YXJ0aW5nIHdpdGggYHNvdXJjZWAsIGFwcGx5IGVhY2ggdHJhbnNmb3JtIHRvIHRoZSByZXN1bHQgb2YgdGhlXG4gICAqIHByZXZpb3VzIG9uZSwgcmV0dXJuaW5nIHRoZSByZXN1bHQgb2YgdGhlIGxhc3QgdHJhbnNmb3JtYXRpb24uXG4gICAqXG4gICAqIEBwYXJhbSB7c3RyaW5nfSBzb3VyY2VcbiAgICogQHBhcmFtIHsoKHN0cjogc3RyaW5nKSA9PiBzdHJpbmcpW119IHRyYW5zZm9ybXNcbiAgICogQHJldHVybnMge3N0cmluZ31cbiAgICovXG4gIGZ1bmN0aW9uIGFwcGx5VHJhbnNmb3Jtcyhzb3VyY2UsIHRyYW5zZm9ybXMpIHtcbiAgICBmb3IgKGNvbnN0IHRyYW5zZm9ybSBvZiB0cmFuc2Zvcm1zKSB7XG4gICAgICBzb3VyY2UgPSB0cmFuc2Zvcm0oc291cmNlKTtcbiAgICB9XG4gICAgcmV0dXJuIHNvdXJjZTtcbiAgfVxuXG4gIC8vIFRoZSBvcmlnaW5hbCB1bnNhZmUgdW50YW1lZCBGdW5jdGlvbiBjb25zdHJ1Y3Rvciwgd2hpY2ggbXVzdCBub3QgZXNjYXBlLlxuICAvLyBTYW1wbGUgYXQgbW9kdWxlIGluaXRpYWxpemF0aW9uIHRpbWUsIHdoaWNoIGlzIGJlZm9yZSBsb2NrZG93biBjYW5cbiAgLy8gcmVwYWlyIGl0LiBVc2UgaXQgb25seSB0byBidWlsZCBwb3dlcmxlc3MgYWJzdHJhY3Rpb25zLlxuICBjb25zdCBGRVJBTF9GVU5DVElPTiA9IEZ1bmN0aW9uO1xuXG4gIC8qKlxuICAgKiBidWlsZE9wdGltaXplcigpXG4gICAqIEdpdmVuIGFuIGFycmF5IG9mIGluZGVudGlmaWVyLCB0aGUgb3B0aW1pemVyIHJldHVybiBhIGBjb25zdGAgZGVjbGFyYXRpb25cbiAgICogZGVzdHJ1Y3RyaW5nIGB0aGlzYC5cbiAgICpcbiAgICogQHBhcmFtIHtBcnJheTxzdHJpbmc+fSBjb25zdGFudHNcbiAgICovXG4gIGZ1bmN0aW9uIGJ1aWxkT3B0aW1pemVyKGNvbnN0YW50cykge1xuICAgIC8vIE5vIG5lZWQgdG8gYnVpbGQgYW4gb3ByaW1pemVyIHdoZW4gdGhlcmUgYXJlIG5vIGNvbnN0YW50cy5cbiAgICBpZiAoY29uc3RhbnRzLmxlbmd0aCA9PT0gMCkgcmV0dXJuICcnO1xuICAgIC8vIFVzZSAndGhpcycgdG8gYXZvaWQgZ29pbmcgdGhyb3VnaCB0aGUgc2NvcGUgcHJveHksIHdoaWNoIGlzIHVuZWNlc3NhcnlcbiAgICAvLyBzaW5jZSB0aGUgb3B0aW1pemVyIG9ubHkgbmVlZHMgcmVmZXJlbmNlcyB0byB0aGUgc2FmZSBnbG9iYWwuXG4gICAgcmV0dXJuIGBjb25zdCB7JHthcnJheUpvaW4oY29uc3RhbnRzLCAnLCcpfX0gPSB0aGlzO2A7XG4gIH1cblxuICAvKipcbiAgICogbWFrZUV2YWx1YXRlRmFjdG9yeSgpXG4gICAqIFRoZSBmYWN0b3J5IGNyZWF0ZSAnZXZhbHVhdGUnIGZ1bmN0aW9ucyB3aXRoIHRoZSBjb3JyZWN0IG9wdGltaXplclxuICAgKiBpbnNlcnRlZC5cbiAgICpcbiAgICogQHBhcmFtIHtBcnJheTxzdHJpbmc+fSBbY29uc3RhbnRzXVxuICAgKi9cbiAgZnVuY3Rpb24gbWFrZUV2YWx1YXRlRmFjdG9yeShjb25zdGFudHMgPSBbXSkge1xuICAgIGNvbnN0IG9wdGltaXplciA9IGJ1aWxkT3B0aW1pemVyKGNvbnN0YW50cyk7XG5cbiAgICAvLyBDcmVhdGUgYSBmdW5jdGlvbiBpbiBzbG9wcHkgbW9kZSwgc28gdGhhdCB3ZSBjYW4gdXNlICd3aXRoJy4gSXQgcmV0dXJuc1xuICAgIC8vIGEgZnVuY3Rpb24gaW4gc3RyaWN0IG1vZGUgdGhhdCBldmFsdWF0ZXMgdGhlIHByb3ZpZGVkIGNvZGUgdXNpbmcgZGlyZWN0XG4gICAgLy8gZXZhbCwgYW5kIHRodXMgaW4gc3RyaWN0IG1vZGUgaW4gdGhlIHNhbWUgc2NvcGUuIFdlIG11c3QgYmUgdmVyeSBjYXJlZnVsXG4gICAgLy8gdG8gbm90IGNyZWF0ZSBuZXcgbmFtZXMgaW4gdGhpcyBzY29wZVxuXG4gICAgLy8gMTogd2UgdXNlICd3aXRoJyAoYXJvdW5kIGEgUHJveHkpIHRvIGNhdGNoIGFsbCBmcmVlIHZhcmlhYmxlIG5hbWVzLiBUaGVcbiAgICAvLyBgdGhpc2AgdmFsdWUgaG9sZHMgdGhlIFByb3h5IHdoaWNoIHNhZmVseSB3cmFwcyB0aGUgc2FmZUdsb2JhbFxuICAgIC8vIDI6ICdvcHRpbWl6ZXInIGNhdGNoZXMgY29uc3RhbnQgdmFyaWFibGUgbmFtZXMgZm9yIHNwZWVkLlxuICAgIC8vIDM6IFRoZSBpbm5lciBzdHJpY3QgZnVuY3Rpb24gaXMgZWZmZWN0aXZlbHkgcGFzc2VkIHR3byBwYXJhbWV0ZXJzOlxuICAgIC8vICAgIGEpIGl0cyBhcmd1bWVudHNbMF0gaXMgdGhlIHNvdXJjZSB0byBiZSBkaXJlY3RseSBldmFsdWF0ZWQuXG4gICAgLy8gICAgYikgaXRzICd0aGlzJyBpcyB0aGUgdGhpcyBiaW5kaW5nIHNlZW4gYnkgdGhlIGNvZGUgYmVpbmdcbiAgICAvLyAgICAgICBkaXJlY3RseSBldmFsdWF0ZWQgKHRoZSBnbG9iYWxPYmplY3QpLlxuICAgIC8vIDQ6IFRoZSBvdXRlciBzbG9wcHkgZnVuY3Rpb24gaXMgcGFzc2VkIG9uZSBwYXJhbWV0ZXIsIHRoZSBzY29wZSBwcm94eS5cbiAgICAvLyAgICBhcyB0aGUgYHRoaXNgIHBhcmFtZXRlci5cblxuICAgIC8vIE5vdGVzOlxuICAgIC8vIC0gZXZlcnl0aGluZyBpbiB0aGUgJ29wdGltaXplcicgc3RyaW5nIGlzIGxvb2tlZCB1cCBpbiB0aGUgcHJveHlcbiAgICAvLyAgIChpbmNsdWRpbmcgYW4gJ2FyZ3VtZW50c1swXScsIHdoaWNoIHBvaW50cyBhdCB0aGUgUHJveHkpLlxuICAgIC8vIC0ga2V5d29yZHMgbGlrZSAnZnVuY3Rpb24nIHdoaWNoIGFyZSByZXNlcnZlZCBrZXl3b3JkcywgYW5kIGNhbm5vdCBiZVxuICAgIC8vICAgdXNlZCBhcyBhIHZhcmlhYmxlcywgc28gdGhleSBpcyBub3QgcGFydCB0byB0aGUgb3B0aW1pemVyLlxuICAgIC8vIC0gd2hlbiAnZXZhbCcgaXMgbG9va2VkIHVwIGluIHRoZSBwcm94eSwgYW5kIGl0J3MgdGhlIGZpcnN0IHRpbWUgaXQgaXNcbiAgICAvLyAgIGxvb2tlZCB1cCBhZnRlciB1c2VVbnNhZmVFdmFsdWF0b3IgaXMgdHVybmVkIG9uLCB0aGUgcHJveHkgcmV0dXJucyB0aGVcbiAgICAvLyAgIGV2YWwgaW50cmluc2ljLCBhbmQgZmxpcHMgdXNlVW5zYWZlRXZhbHVhdG9yIGJhY2sgdG8gZmFsc2UuIEFueSByZWZlcmVuY2VcbiAgICAvLyAgIHRvICdldmFsJyBpbiB0aGF0IHN0cmluZyB3aWxsIGdldCB0aGUgdGFtZWQgZXZhbHVhdG9yLlxuXG4gICAgcmV0dXJuIEZFUkFMX0ZVTkNUSU9OKGBcbiAgICB3aXRoICh0aGlzKSB7XG4gICAgICAke29wdGltaXplcn1cbiAgICAgIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICAgICAgJ3VzZSBzdHJpY3QnO1xuICAgICAgICByZXR1cm4gZXZhbChhcmd1bWVudHNbMF0pO1xuICAgICAgfTtcbiAgICB9XG4gIGApO1xuICB9XG5cbiAgLy8gUG9ydGlvbnMgYWRhcHRlZCBmcm9tIFY4IC0gQ29weXJpZ2h0IDIwMTYgdGhlIFY4IHByb2plY3QgYXV0aG9ycy5cblxuICBjb25zdCB7IGRldGFpbHM6IGQkMiB9ID0gYXNzZXJ0O1xuXG4gIC8qKlxuICAgKiBwZXJmb3JtRXZhbCgpXG4gICAqIFRoZSBsb3ctbGV2ZWwgb3BlcmF0aW9uIHVzZWQgYnkgYWxsIGV2YWx1YXRvcnM6XG4gICAqIGV2YWwoKSwgRnVuY3Rpb24oKSwgRXZhbHV0YXRvci5wcm90b3R5cGUuZXZhbHVhdGUoKS5cbiAgICpcbiAgICogQHBhcmFtIHtzdHJpbmd9IHNvdXJjZVxuICAgKiBAcGFyYW0ge09iamVjdH0gZ2xvYmFsT2JqZWN0XG4gICAqIEBwYXJhbSB7T2JqZWVjdH0gbG9jYWxPYmplY3RcbiAgICogQHBhcmFtIHtPYmplY3R9IFtvcHRpb25zXVxuICAgKiBAcGFyYW0ge0FycmF5PFRyYW5zZm9ybT59IFtvcHRpb25zLmxvY2FsVHJhbnNmb3Jtc11cbiAgICogQHBhcmFtIHtBcnJheTxUcmFuc2Zvcm0+fSBbb3B0aW9ucy5nbG9iYWxUcmFuc2Zvcm1zXVxuICAgKiBAcGFyYW0ge2Jvb2x9IFtvcHRpb25zLnNsb3BweUdsb2JhbHNNb2RlXVxuICAgKiBAcGFyYW0ge1dlYWtTZXR9IFtvcHRpb25zLmtub3duU2NvcGVQcm94aWVzXVxuICAgKi9cbiAgZnVuY3Rpb24gcGVyZm9ybUV2YWwoXG4gICAgc291cmNlLFxuICAgIGdsb2JhbE9iamVjdCxcbiAgICBsb2NhbE9iamVjdCA9IHt9LFxuICAgIHtcbiAgICAgIGxvY2FsVHJhbnNmb3JtcyA9IFtdLFxuICAgICAgZ2xvYmFsVHJhbnNmb3JtcyA9IFtdLFxuICAgICAgc2xvcHB5R2xvYmFsc01vZGUgPSBmYWxzZSxcbiAgICAgIGtub3duU2NvcGVQcm94aWVzID0gbmV3IFdlYWtTZXQoKSxcbiAgICB9ID0ge30sXG4gICkge1xuICAgIC8vIEV4ZWN1dGUgdGhlIG1hbmRhdG9yeSB0cmFuc2Zvcm1zIGxhc3QgdG8gZW5zdXJlIHRoYXQgYW55IHJld3JpdHRlbiBjb2RlXG4gICAgLy8gbWVldHMgdGhvc2UgbWFuZGF0b3J5IHJlcXVpcmVtZW50cy5cbiAgICBzb3VyY2UgPSBhcHBseVRyYW5zZm9ybXMoc291cmNlLCBbXG4gICAgICAuLi5sb2NhbFRyYW5zZm9ybXMsXG4gICAgICAuLi5nbG9iYWxUcmFuc2Zvcm1zLFxuICAgICAgbWFuZGF0b3J5VHJhbnNmb3JtcyxcbiAgICBdKTtcblxuICAgIGNvbnN0IHNjb3BlSGFuZGxlciA9IGNyZWF0ZVNjb3BlSGFuZGxlcihnbG9iYWxPYmplY3QsIGxvY2FsT2JqZWN0LCB7XG4gICAgICBzbG9wcHlHbG9iYWxzTW9kZSxcbiAgICB9KTtcbiAgICBjb25zdCBzY29wZVByb3h5UmV2b2NhYmxlID0gcHJveHlSZXZvY2FibGUoaW1tdXRhYmxlT2JqZWN0LCBzY29wZUhhbmRsZXIpO1xuICAgIC8vIEVuc3VyZSB0aGF0IFwidGhpc1wiIHJlc29sdmVzIHRvIHRoZSBzY29wZSBwcm94eS5cblxuICAgIGNvbnN0IGNvbnN0YW50cyA9IGdldFNjb3BlQ29uc3RhbnRzKGdsb2JhbE9iamVjdCwgbG9jYWxPYmplY3QpO1xuICAgIGNvbnN0IGV2YWx1YXRlRmFjdG9yeSA9IG1ha2VFdmFsdWF0ZUZhY3RvcnkoY29uc3RhbnRzKTtcbiAgICBjb25zdCBldmFsdWF0ZSA9IGFwcGx5KGV2YWx1YXRlRmFjdG9yeSwgc2NvcGVQcm94eVJldm9jYWJsZS5wcm94eSwgW10pO1xuXG4gICAgc2NvcGVIYW5kbGVyLnVzZVVuc2FmZUV2YWx1YXRvciA9IHRydWU7XG4gICAgbGV0IGVycjtcbiAgICB0cnkge1xuICAgICAgLy8gRW5zdXJlIHRoYXQgXCJ0aGlzXCIgcmVzb2x2ZXMgdG8gdGhlIHNhZmUgZ2xvYmFsLlxuICAgICAga25vd25TY29wZVByb3hpZXMuYWRkKHNjb3BlUHJveHlSZXZvY2FibGUucHJveHkpO1xuICAgICAgcmV0dXJuIGFwcGx5KGV2YWx1YXRlLCBnbG9iYWxPYmplY3QsIFtzb3VyY2VdKTtcbiAgICB9IGNhdGNoIChlKSB7XG4gICAgICAvLyBzdGFzaCB0aGUgY2hpbGQtY29kZSBlcnJvciBpbiBob3BlcyBvZiBkZWJ1Z2dpbmcgdGhlIGludGVybmFsIGZhaWx1cmVcbiAgICAgIGVyciA9IGU7XG4gICAgICB0aHJvdyBlO1xuICAgIH0gZmluYWxseSB7XG4gICAgICBpZiAoc2NvcGVIYW5kbGVyLnVzZVVuc2FmZUV2YWx1YXRvciA9PT0gdHJ1ZSkge1xuICAgICAgICAvLyBUaGUgcHJveHkgc3dpdGNoZXMgb2ZmIHVzZVVuc2FmZUV2YWx1YXRvciBpbW1lZGlhdGVseSBhZnRlclxuICAgICAgICAvLyB0aGUgZmlyc3QgYWNjZXNzLCBidXQgaWYgdGhhdCdzIG5vdCB0aGUgY2FzZSB3ZSBzaG91bGQgYWJvcnQuXG4gICAgICAgIC8vIFRoaXMgY29uZGl0aW9uIGlzIG9uZSB3aGVyZSB0aGlzIHZhdCBpcyBub3cgaG9wZWxlc3NseSBjb25mdXNlZCxcbiAgICAgICAgLy8gYW5kIHRoZSB2YXQgYXMgYSB3aG9sZSBzaG91bGQgYmUgYWJvcnRlZC4gQWxsIGltbWVkaWF0ZWx5IHJlYWNoYWJsZVxuICAgICAgICAvLyBzdGF0ZSBzaG91bGQgYmUgYWJhbmRvbmVkLiBIb3dldmVyLCB0aGF0IGlzIG5vdCB5ZXQgcG9zc2libGUsXG4gICAgICAgIC8vIHNvIHdlIGF0IGxlYXN0IHByZXZlbnQgZnVydGhlciB2YXJpYWJsZSByZXNvbHV0aW9uIHZpYSB0aGVcbiAgICAgICAgLy8gc2NvcGVIYW5kbGVyLCBhbmQgdGhyb3cgYW4gZXJyb3Igd2l0aCBkaWFnbm9zdGljIGluZm8gaW5jbHVkaW5nXG4gICAgICAgIC8vIHRoZSB0aHJvd24gZXJyb3IgaWYgYW55IGZyb20gZXZhbHVhdGluZyB0aGUgc291cmNlIGNvZGUuXG4gICAgICAgIHNjb3BlUHJveHlSZXZvY2FibGUucmV2b2tlKCk7XG4gICAgICAgIC8vIFRPRE8gQSBHT09EIFBMQUNFIFRPIFBBTklDKCksIGkuZS4sIGtpbGwgdGhlIHZhdCBpbmNhcm5hdGlvbi5cbiAgICAgICAgLy8gU2VlIGh0dHBzOi8vZ2l0aHViLmNvbS9BZ29yaWMvU0VTLXNoaW0vaXNzdWVzLzQ5MFxuICAgICAgICBhc3NlcnQuZmFpbChkJDJgaGFuZGxlciBkaWQgbm90IHJldm9rZSB1c2VVbnNhZmVFdmFsdWF0b3IgJHtlcnJ9YCk7XG4gICAgICB9XG4gICAgfVxuICB9XG5cbiAgLypcbiAgICogbWFrZUV2YWxGdW5jdGlvbigpXG4gICAqIEEgc2FmZSB2ZXJzaW9uIG9mIHRoZSBuYXRpdmUgZXZhbCBmdW5jdGlvbiB3aGljaCByZWxpZXMgb25cbiAgICogdGhlIHNhZmV0eSBvZiBwZXJmb3JtRXZhbCBmb3IgY29uZmluZW1lbnQuXG4gICAqL1xuICBjb25zdCBtYWtlRXZhbEZ1bmN0aW9uID0gKGdsb2JhbE9iamVjdCwgb3B0aW9ucyA9IHt9KSA9PiB7XG4gICAgLy8gV2UgdXNlIHRoZSB0aGUgY29uY2lzZSBtZXRob2Qgc3ludGF4IHRvIGNyZWF0ZSBhbiBldmFsIHdpdGhvdXQgYVxuICAgIC8vIFtbQ29uc3RydWN0XV0gYmVoYXZpb3IgKHN1Y2ggdGhhdCB0aGUgaW52b2NhdGlvbiBcIm5ldyBldmFsKClcIiB0aHJvd3NcbiAgICAvLyBUeXBlRXJyb3I6IGV2YWwgaXMgbm90IGEgY29uc3RydWN0b3JcIiksIGJ1dCB3aGljaCBzdGlsbCBhY2NlcHRzIGFcbiAgICAvLyAndGhpcycgYmluZGluZy5cbiAgICBjb25zdCBuZXdFdmFsID0ge1xuICAgICAgZXZhbChzb3VyY2UpIHtcbiAgICAgICAgaWYgKHR5cGVvZiBzb3VyY2UgIT09ICdzdHJpbmcnKSB7XG4gICAgICAgICAgLy8gQXMgcGVyIHRoZSBydW50aW1lIHNlbWFudGljIG9mIFBlcmZvcm1FdmFsIFtFQ01BU2NyaXB0IDE4LjIuMS4xXTpcbiAgICAgICAgICAvLyBJZiBUeXBlKHNvdXJjZSkgaXMgbm90IFN0cmluZywgcmV0dXJuIHNvdXJjZS5cbiAgICAgICAgICAvLyBUT0RPIFJlY2VudCBwcm9wb3NhbHMgZnJvbSBNaWtlIFNhbXVlbCBtYXkgY2hhbmdlIHRoaXMgbm9uLXN0cmluZ1xuICAgICAgICAgIC8vIHJ1bGUuIFRyYWNrLlxuICAgICAgICAgIHJldHVybiBzb3VyY2U7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHBlcmZvcm1FdmFsKHNvdXJjZSwgZ2xvYmFsT2JqZWN0LCB7fSwgb3B0aW9ucyk7XG4gICAgICB9LFxuICAgIH0uZXZhbDtcblxuICAgIHJldHVybiBuZXdFdmFsO1xuICB9O1xuXG4gIC8vIFRoZSBvcmlnaW5hbCB1bnNhZmUgdW50YW1lZCBGdW5jdGlvbiBjb25zdHJ1Y3Rvciwgd2hpY2ggbXVzdCBub3QgZXNjYXBlLlxuICAvLyBTYW1wbGUgYXQgbW9kdWxlIGluaXRpYWxpemF0aW9uIHRpbWUsIHdoaWNoIGlzIGJlZm9yZSBsb2NrZG93biBjYW5cbiAgLy8gcmVwYWlyIGl0LiAgVXNlIGl0IG9ubHkgdG8gYnVpbGQgcG93ZXJsZXNzIGFic3RyYWN0aW9ucy5cbiAgY29uc3QgRkVSQUxfRlVOQ1RJT04kMSA9IEZ1bmN0aW9uO1xuXG4gIC8qXG4gICAqIG1ha2VGdW5jdGlvbkNvbnN0cnVjdG9yKClcbiAgICogQSBzYWZlIHZlcnNpb24gb2YgdGhlIG5hdGl2ZSBGdW5jdGlvbiB3aGljaCByZWxpZXMgb25cbiAgICogdGhlIHNhZmV0eSBvZiBwZXJmb3JtRXZhbCBmb3IgY29uZmluZW1lbnQuXG4gICAqL1xuICBmdW5jdGlvbiBtYWtlRnVuY3Rpb25Db25zdHJ1Y3RvcihnbG9iYU9iamVjdCwgb3B0aW9ucyA9IHt9KSB7XG4gICAgLy8gRGVmaW5lIGFuIHVudXNlZCBwYXJhbWV0ZXIgdG8gZW5zdXJlIEZ1bmN0aW9uLmxlbmd0aCA9PT0gMVxuICAgIGNvbnN0IG5ld0Z1bmN0aW9uID0gZnVuY3Rpb24gRnVuY3Rpb24oX2JvZHkpIHtcbiAgICAgIC8vIFNhbml0aXplIGFsbCBwYXJhbWV0ZXJzIGF0IHRoZSBlbnRyeSBwb2ludC5cbiAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBwcmVmZXItcmVzdC1wYXJhbXNcbiAgICAgIGNvbnN0IGJvZHlUZXh0ID0gYCR7YXJyYXlQb3AoYXJndW1lbnRzKSB8fCAnJ31gO1xuICAgICAgLy8gZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIHByZWZlci1yZXN0LXBhcmFtc1xuICAgICAgY29uc3QgcGFyYW1ldGVycyA9IGAke2FycmF5Sm9pbihhcmd1bWVudHMsICcsJyl9YDtcblxuICAgICAgLy8gQXJlIHBhcmFtZXRlcnMgYW5kIGJvZHlUZXh0IHZhbGlkIGNvZGUsIG9yIGlzIHNvbWVvbmVcbiAgICAgIC8vIGF0dGVtcHRpbmcgYW4gaW5qZWN0aW9uIGF0dGFjaz8gVGhpcyB3aWxsIHRocm93IGEgU3ludGF4RXJyb3IgaWY6XG4gICAgICAvLyAtIHBhcmFtZXRlcnMgZG9lc24ndCBwYXJzZSBhcyBwYXJhbWV0ZXJzXG4gICAgICAvLyAtIGJvZHlUZXh0IGRvZXNuJ3QgcGFyc2UgYXMgYSBmdW5jdGlvbiBib2R5XG4gICAgICAvLyAtIGVpdGhlciBjb250YWluIGEgY2FsbCB0byBzdXBlcigpIG9yIHJlZmVyZW5jZXMgYSBzdXBlciBwcm9wZXJ0eS5cbiAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1uZXdcbiAgICAgIG5ldyBGRVJBTF9GVU5DVElPTiQxKHBhcmFtZXRlcnMsIGJvZHlUZXh0KTtcblxuICAgICAgLy8gU2FmZSB0byBiZSBjb21iaW5lZC4gRGVmZWF0IHBvdGVudGlhbCB0cmFpbGluZyBjb21tZW50cy5cbiAgICAgIC8vIFRPRE86IHNpbmNlIHdlIGNyZWF0ZSBhbiBhbm9ueW1vdXMgZnVuY3Rpb24sIHRoZSAndGhpcycgdmFsdWVcbiAgICAgIC8vIGlzbid0IGJvdW5kIHRvIHRoZSBnbG9iYWwgb2JqZWN0IGFzIHBlciBzcGVjcywgYnV0IHNldCBhcyB1bmRlZmluZWQuXG4gICAgICBjb25zdCBzcmMgPSBgKGZ1bmN0aW9uIGFub255bW91cygke3BhcmFtZXRlcnN9XFxuKSB7XFxuJHtib2R5VGV4dH1cXG59KWA7XG4gICAgICByZXR1cm4gcGVyZm9ybUV2YWwoc3JjLCBnbG9iYU9iamVjdCwge30sIG9wdGlvbnMpO1xuICAgIH07XG5cbiAgICBkZWZpbmVQcm9wZXJ0aWVzKG5ld0Z1bmN0aW9uLCB7XG4gICAgICAvLyBFbnN1cmUgdGhhdCBhbnkgZnVuY3Rpb24gY3JlYXRlZCBpbiBhbnkgZXZhbHVhdG9yIGluIGEgcmVhbG0gaXMgYW5cbiAgICAgIC8vIGluc3RhbmNlIG9mIEZ1bmN0aW9uIGluIGFueSBldmFsdWF0b3Igb2YgdGhlIHNhbWUgcmVhbG0uXG4gICAgICBwcm90b3R5cGU6IHtcbiAgICAgICAgdmFsdWU6IEZ1bmN0aW9uLnByb3RvdHlwZSxcbiAgICAgICAgd3JpdGFibGU6IGZhbHNlLFxuICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiBmYWxzZSxcbiAgICAgIH0sXG4gICAgfSk7XG5cbiAgICAvLyBBc3NlcnQgaWRlbnRpdHkgb2YgRnVuY3Rpb24uX19wcm90b19fIGFjY3Jvc3MgYWxsIGNvbXBhcnRtZW50c1xuICAgIGFzc2VydChcbiAgICAgIGdldFByb3RvdHlwZU9mKEZ1bmN0aW9uKSA9PT0gRnVuY3Rpb24ucHJvdG90eXBlLFxuICAgICAgJ0Z1bmN0aW9uIHByb3RvdHlwZSBpcyB0aGUgc2FtZSBhY2Nyb3NzIGNvbXBhcnRtZW50cycsXG4gICAgKTtcbiAgICBhc3NlcnQoXG4gICAgICBnZXRQcm90b3R5cGVPZihuZXdGdW5jdGlvbikgPT09IEZ1bmN0aW9uLnByb3RvdHlwZSxcbiAgICAgICdGdW5jdGlvbiBjb25zdHJ1Y3RvciBwcm90b3R5cGUgaXMgdGhlIHNhbWUgYWNjcm9zcyBjb21wYXJ0bWVudHMnLFxuICAgICk7XG5cbiAgICByZXR1cm4gbmV3RnVuY3Rpb247XG4gIH1cblxuICAvKipcbiAgICogaW5pdEdsb2JhbE9iamVjdCgpXG4gICAqIENyZWF0ZSBuZXcgZ2xvYmFsIG9iamVjdCB1c2luZyBhIHByb2Nlc3Mgc2ltaWxhciB0byBFQ01BIHNwZWNpZmljYXRpb25zXG4gICAqIChwb3J0aW9ucyBvZiBTZXRSZWFsbUdsb2JhbE9iamVjdCBhbmQgU2V0RGVmYXVsdEdsb2JhbEJpbmRpbmdzKS5cbiAgICogYG5ld0dsb2JhbFByb3BlcnR5TmFtZXNgIHNob3VsZCBiZSBlaXRoZXIgYGluaXRpYWxHbG9iYWxQcm9wZXJ0eU5hbWVzYCBvclxuICAgKiBgc2hhcmVkR2xvYmFsUHJvcGVydHlOYW1lc2AuXG4gICAqXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBnbG9iYWxPYmplY3RcbiAgICogQHBhcmFtIHtPYmplY3R9IGludHJpbnNpY3NcbiAgICogQHBhcmFtIHtPYmplY3R9IG5ld0dsb2JhbFByb3BlcnR5TmFtZXNcbiAgICogQHBhcmFtIHtGdW5jdGlvbn0gbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3JcbiAgICogQHBhcmFtIHtPYmplY3R9IGNvbXBhcnRtZW50UHJvdG90eXBlXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBbb3B0aW9uc11cbiAgICogQHBhcmFtIHtBcnJheTxUcmFuc2Zvcm0+fSBbb3B0aW9ucy5nbG9iYWxUcmFuc2Zvcm1zXVxuICAgKiBAcGFyYW0geyhPYmplY3QpID0+IHZvaWR9IFtvcHRpb25zLm5hdGl2ZUJyYW5kZXJdXG4gICAqL1xuICBmdW5jdGlvbiBpbml0R2xvYmFsT2JqZWN0KFxuICAgIGdsb2JhbE9iamVjdCxcbiAgICBpbnRyaW5zaWNzLFxuICAgIG5ld0dsb2JhbFByb3BlcnR5TmFtZXMsXG4gICAgbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3IsXG4gICAgY29tcGFydG1lbnRQcm90b3R5cGUsXG4gICAgeyBnbG9iYWxUcmFuc2Zvcm1zLCBuYXRpdmVCcmFuZGVyIH0sXG4gICkge1xuICAgIGZvciAoY29uc3QgW25hbWUsIGNvbnN0YW50XSBvZiBlbnRyaWVzKGNvbnN0YW50UHJvcGVydGllcykpIHtcbiAgICAgIGRlZmluZVByb3BlcnR5KGdsb2JhbE9iamVjdCwgbmFtZSwge1xuICAgICAgICB2YWx1ZTogY29uc3RhbnQsXG4gICAgICAgIHdyaXRhYmxlOiBmYWxzZSxcbiAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgIGNvbmZpZ3VyYWJsZTogZmFsc2UsXG4gICAgICB9KTtcbiAgICB9XG5cbiAgICBmb3IgKGNvbnN0IFtuYW1lLCBpbnRyaW5zaWNOYW1lXSBvZiBlbnRyaWVzKHVuaXZlcnNhbFByb3BlcnR5TmFtZXMpKSB7XG4gICAgICBpZiAob2JqZWN0SGFzT3duUHJvcGVydHkoaW50cmluc2ljcywgaW50cmluc2ljTmFtZSkpIHtcbiAgICAgICAgZGVmaW5lUHJvcGVydHkoZ2xvYmFsT2JqZWN0LCBuYW1lLCB7XG4gICAgICAgICAgdmFsdWU6IGludHJpbnNpY3NbaW50cmluc2ljTmFtZV0sXG4gICAgICAgICAgd3JpdGFibGU6IHRydWUsXG4gICAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlLFxuICAgICAgICB9KTtcbiAgICAgIH1cbiAgICB9XG5cbiAgICBmb3IgKGNvbnN0IFtuYW1lLCBpbnRyaW5zaWNOYW1lXSBvZiBlbnRyaWVzKG5ld0dsb2JhbFByb3BlcnR5TmFtZXMpKSB7XG4gICAgICBpZiAob2JqZWN0SGFzT3duUHJvcGVydHkoaW50cmluc2ljcywgaW50cmluc2ljTmFtZSkpIHtcbiAgICAgICAgZGVmaW5lUHJvcGVydHkoZ2xvYmFsT2JqZWN0LCBuYW1lLCB7XG4gICAgICAgICAgdmFsdWU6IGludHJpbnNpY3NbaW50cmluc2ljTmFtZV0sXG4gICAgICAgICAgd3JpdGFibGU6IHRydWUsXG4gICAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlLFxuICAgICAgICB9KTtcbiAgICAgIH1cbiAgICB9XG5cbiAgICBjb25zdCBwZXJDb21wYXJ0bWVudEdsb2JhbHMgPSB7XG4gICAgICBnbG9iYWxUaGlzOiBnbG9iYWxPYmplY3QsXG4gICAgICBldmFsOiBtYWtlRXZhbEZ1bmN0aW9uKGdsb2JhbE9iamVjdCwge1xuICAgICAgICBnbG9iYWxUcmFuc2Zvcm1zLFxuICAgICAgfSksXG4gICAgICBGdW5jdGlvbjogbWFrZUZ1bmN0aW9uQ29uc3RydWN0b3IoZ2xvYmFsT2JqZWN0LCB7XG4gICAgICAgIGdsb2JhbFRyYW5zZm9ybXMsXG4gICAgICB9KSxcbiAgICB9O1xuXG4gICAgcGVyQ29tcGFydG1lbnRHbG9iYWxzLkNvbXBhcnRtZW50ID0gbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3IoXG4gICAgICBtYWtlQ29tcGFydG1lbnRDb25zdHJ1Y3RvcixcbiAgICAgIGludHJpbnNpY3MsXG4gICAgICBuYXRpdmVCcmFuZGVyLFxuICAgICk7XG5cbiAgICAvLyBUT0RPIFRoZXNlIHNob3VsZCBzdGlsbCBiZSB0YW1lZCBhY2NvcmRpbmcgdG8gdGhlIHdoaXRlbGlzdCBiZWZvcmVcbiAgICAvLyBiZWluZyBtYWRlIGF2YWlsYWJsZS5cbiAgICBmb3IgKGNvbnN0IFtuYW1lLCB2YWx1ZV0gb2YgZW50cmllcyhwZXJDb21wYXJ0bWVudEdsb2JhbHMpKSB7XG4gICAgICBkZWZpbmVQcm9wZXJ0eShnbG9iYWxPYmplY3QsIG5hbWUsIHtcbiAgICAgICAgdmFsdWUsXG4gICAgICAgIHdyaXRhYmxlOiB0cnVlLFxuICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlLFxuICAgICAgfSk7XG4gICAgICBpZiAodHlwZW9mIHZhbHVlID09PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgIG5hdGl2ZUJyYW5kZXIodmFsdWUpO1xuICAgICAgfVxuICAgIH1cbiAgfVxuXG4gIC8vIEB0cy1jaGVja1xuXG4gIC8vIEZvciBvdXIgaW50ZXJuYWwgZGVidWdnaW5nIHB1cnBvc2VzLCB1bmNvbW1lbnRcbiAgLy8gY29uc3QgaW50ZXJuYWxEZWJ1Z0NvbnNvbGUgPSBjb25zb2xlO1xuXG4gIC8vIFRoZSB3aGl0ZWxpc3RzIG9mIGNvbnNvbGUgbWV0aG9kcywgZnJvbTpcbiAgLy8gV2hhdHdnIFwibGl2aW5nIHN0YW5kYXJkXCIgaHR0cHM6Ly9jb25zb2xlLnNwZWMud2hhdHdnLm9yZy9cbiAgLy8gTm9kZSBodHRwczovL25vZGVqcy5vcmcvZGlzdC9sYXRlc3QtdjE0LngvZG9jcy9hcGkvY29uc29sZS5odG1sXG4gIC8vIE1ETiBodHRwczovL2RldmVsb3Blci5tb3ppbGxhLm9yZy9lbi1VUy9kb2NzL1dlYi9BUEkvQ29uc29sZV9BUElcbiAgLy8gVHlwZVNjcmlwdCBodHRwczovL29wZW5zdGFwcHMuZ2l0bGFiLmlvL3Byb2plY3RtYW5hZ2VtZW50L2ludGVyZmFjZXMvX25vZGVfbW9kdWxlc19fdHlwZXNfbm9kZV9nbG9iYWxzX2RfLmNvbnNvbGUuaHRtbFxuICAvLyBDaHJvbWUgaHR0cHM6Ly9kZXZlbG9wZXJzLmdvb2dsZS5jb20vd2ViL3Rvb2xzL2Nocm9tZS1kZXZ0b29scy9jb25zb2xlL2FwaVxuXG4gIC8vIEFsbCBjb25zb2xlIGxldmVsIG1ldGhvZHMgaGF2ZSBwYXJhbWV0ZXJzIChmbXQ/LCAuLi5hcmdzKVxuICAvLyB3aGVyZSB0aGUgYXJndW1lbnQgc2VxdWVuY2UgYGZtdD8sIC4uLmFyZ3NgIGZvcm1hdHMgYXJncyBhY2NvcmRpbmcgdG9cbiAgLy8gZm10IGlmIGZtdCBpcyBhIGZvcm1hdCBzdHJpbmcuIE90aGVyd2lzZSwgaXQganVzdCByZW5kZXJzIHRoZW0gYWxsIGFzIHZhbHVlc1xuICAvLyBzZXBhcmF0ZWQgYnkgc3BhY2VzLlxuICAvLyBodHRwczovL2NvbnNvbGUuc3BlYy53aGF0d2cub3JnLyNmb3JtYXR0ZXJcbiAgLy8gaHR0cHM6Ly9ub2RlanMub3JnL2RvY3MvbGF0ZXN0L2FwaS91dGlsLmh0bWwjdXRpbF91dGlsX2Zvcm1hdF9mb3JtYXRfYXJnc1xuXG4gIC8vIEZvciB0aGUgY2F1c2FsIGNvbnNvbGUsIGFsbCBvY2N1cnJlbmNlcyBvZiBgZm10LCAuLi5hcmdzYCBvciBgLi4uYXJnc2AgYnlcbiAgLy8gaXRzZWxmIG11c3QgY2hlY2sgZm9yIHRoZSBwcmVzZW5jZSBvZiBhbiBlcnJvciB0byBhc2sgdGhlXG4gIC8vIGBsb2dnZWRFcnJvckhhbmRsZXJgIHRvIGhhbmRsZS5cbiAgLy8gSW4gdGhlb3J5IHdlIHNob3VsZCBkbyBhIGRlZXAgaW5zcGVjdGlvbiB0byBkZXRlY3QgZm9yIGV4YW1wbGUgYW4gYXJyYXlcbiAgLy8gY29udGFpbmluZyBhbiBlcnJvci4gV2UgY3VycmVudGx5IGRvIG5vdCBkZXRlY3QgdGhlc2UgYW5kIG1heSBuZXZlci5cblxuICAvKiogQHR5cGVkZWYge2tleW9mIFZpcnR1YWxDb25zb2xlIHwgJ3Byb2ZpbGUnIHwgJ3Byb2ZpbGVFbmQnfSBDb25zb2xlUHJvcHMgKi9cblxuICAvKiogQHR5cGUge3JlYWRvbmx5IFtDb25zb2xlUHJvcHMsIExvZ1NldmVyaXR5IHwgdW5kZWZpbmVkXVtdfSAqL1xuICBjb25zdCBjb25zb2xlTGV2ZWxNZXRob2RzID0gZnJlZXplKFtcbiAgICBbJ2RlYnVnJywgJ2RlYnVnJ10sIC8vIChmbXQ/LCAuLi5hcmdzKSB2ZXJib3NlIGxldmVsIG9uIENocm9tZVxuICAgIFsnbG9nJywgJ2xvZyddLCAvLyAoZm10PywgLi4uYXJncykgaW5mbyBsZXZlbCBvbiBDaHJvbWVcbiAgICBbJ2luZm8nLCAnaW5mbyddLCAvLyAoZm10PywgLi4uYXJncylcbiAgICBbJ3dhcm4nLCAnd2FybiddLCAvLyAoZm10PywgLi4uYXJncylcbiAgICBbJ2Vycm9yJywgJ2Vycm9yJ10sIC8vIChmbXQ/LCAuLi5hcmdzKVxuXG4gICAgWyd0cmFjZScsICdsb2cnXSwgLy8gKGZtdD8sIC4uLmFyZ3MpXG4gICAgWydkaXJ4bWwnLCAnbG9nJ10sIC8vIChmbXQ/LCAuLi5hcmdzKVxuICAgIFsnZ3JvdXAnLCAnbG9nJ10sIC8vIChmbXQ/LCAuLi5hcmdzKVxuICAgIFsnZ3JvdXBDb2xsYXBzZWQnLCAnbG9nJ10sIC8vIChmbXQ/LCAuLi5hcmdzKVxuICBdKTtcblxuICAvKiogQHR5cGUge3JlYWRvbmx5IFtDb25zb2xlUHJvcHMsIExvZ1NldmVyaXR5IHwgdW5kZWZpbmVkXVtdfSAqL1xuICBjb25zdCBjb25zb2xlT3RoZXJNZXRob2RzID0gZnJlZXplKFtcbiAgICBbJ2Fzc2VydCcsICdlcnJvciddLCAvLyAodmFsdWUsIGZtdD8sIC4uLmFyZ3MpXG4gICAgWyd0aW1lTG9nJywgJ2xvZyddLCAvLyAobGFiZWw/LCAuLi5hcmdzKSBubyBmbXQgc3RyaW5nXG5cbiAgICAvLyBJbnNlbnNpdGl2ZSB0byB3aGV0aGVyIGFueSBhcmd1bWVudCBpcyBhbiBlcnJvci4gQWxsIGFyZ3VtZW50cyBjYW4gcGFzc1xuICAgIC8vIHRocnUgdG8gYmFzZUNvbnNvbGUgYXMgaXMuXG4gICAgWydjbGVhcicsIHVuZGVmaW5lZF0sIC8vICgpXG4gICAgWydjb3VudCcsICdpbmZvJ10sIC8vIChsYWJlbD8pXG4gICAgWydjb3VudFJlc2V0JywgdW5kZWZpbmVkXSwgLy8gKGxhYmVsPylcbiAgICBbJ2RpcicsICdsb2cnXSwgLy8gKGl0ZW0sIG9wdGlvbnM/KVxuICAgIFsnZ3JvdXBFbmQnLCAnbG9nJ10sIC8vICgpXG4gICAgLy8gSW4gdGhlb3J5IHRhYnVsYXIgZGF0YSBtYXkgYmUgb3IgY29udGFpbiBhbiBlcnJvci4gSG93ZXZlciwgd2UgY3VycmVudGx5XG4gICAgLy8gZG8gbm90IGRldGVjdCB0aGVzZSBhbmQgbWF5IG5ldmVyLlxuICAgIFsndGFibGUnLCAnbG9nJ10sIC8vICh0YWJ1bGFyRGF0YSwgcHJvcGVydGllcz8pXG4gICAgWyd0aW1lJywgJ2luZm8nXSwgLy8gKGxhYmVsPylcbiAgICBbJ3RpbWVFbmQnLCAnaW5mbyddLCAvLyAobGFiZWw/KVxuXG4gICAgLy8gTm9kZSBJbnNwZWN0b3Igb25seSwgTUROLCBhbmQgVHlwZVNjcmlwdCwgYnV0IG5vdCB3aGF0d2dcbiAgICBbJ3Byb2ZpbGUnLCB1bmRlZmluZWRdLCAvLyAobGFiZWw/KVxuICAgIFsncHJvZmlsZUVuZCcsIHVuZGVmaW5lZF0sIC8vIChsYWJlbD8pXG4gICAgWyd0aW1lU3RhbXAnLCB1bmRlZmluZWRdLCAvLyAobGFiZWw/KVxuICBdKTtcblxuICAvKiogQHR5cGUge3JlYWRvbmx5IFtDb25zb2xlUHJvcHMsIExvZ1NldmVyaXR5IHwgdW5kZWZpbmVkXVtdfSAqL1xuICBjb25zdCBjb25zb2xlV2hpdGVsaXN0ID0gZnJlZXplKFtcbiAgICAuLi5jb25zb2xlTGV2ZWxNZXRob2RzLFxuICAgIC4uLmNvbnNvbGVPdGhlck1ldGhvZHMsXG4gIF0pO1xuXG4gIC8qKlxuICAgKiBjb25zb2xlT21pdHRlZFByb3BlcnRpZXMgaXMgY3VycmVudGx5IHVudXNlZC4gSSByZWNvcmQgYW5kIG1haW50YWluIGl0IGhlcmVcbiAgICogd2l0aCB0aGUgaW50ZW50aW9uIHRoYXQgaXQgYmUgdHJlYXRlZCBsaWtlIHRoZSBgZmFsc2VgIGVudHJpZXMgaW4gdGhlIG1haW5cbiAgICogU0VTIHdoaXRlbGlzdDogdGhhdCBzZWVpbmcgdGhlc2Ugb24gdGhlIG9yaWdpbmFsIGNvbnNvbGUgaXMgZXhwZWN0ZWQsIGJ1dFxuICAgKiBzZWVpbmcgYW55dGhpbmcgZWxzZSB0aGF0J3Mgb3V0c2lkZSB0aGUgd2hpdGVsaXN0IGlzIHN1cnByaXNpbmcgYW5kIHNob3VsZFxuICAgKiBwcm92aWRlIGEgZGlhZ25vc3RpYy5cbiAgICpcbiAgICogY29uc3QgY29uc29sZU9taXR0ZWRQcm9wZXJ0aWVzID0gZnJlZXplKFtcbiAgICogICAnbWVtb3J5JywgLy8gQ2hyb21lXG4gICAqICAgJ2V4Y2VwdGlvbicsIC8vIEZGLCBNRE5cbiAgICogICAnX2lnbm9yZUVycm9ycycsIC8vIE5vZGVcbiAgICogICAnX3N0ZGVycicsIC8vIE5vZGVcbiAgICogICAnX3N0ZGVyckVycm9ySGFuZGxlcicsIC8vIE5vZGVcbiAgICogICAnX3N0ZG91dCcsIC8vIE5vZGVcbiAgICogICAnX3N0ZG91dEVycm9ySGFuZGxlcicsIC8vIE5vZGVcbiAgICogICAnX3RpbWVzJywgLy8gTm9kZVxuICAgKiAgICdjb250ZXh0JywgLy8gQ2hyb21lLCBOb2RlXG4gICAqICAgJ3JlY29yZCcsIC8vIFNhZmFyaVxuICAgKiAgICdyZWNvcmRFbmQnLCAvLyBTYWZhcmlcbiAgICpcbiAgICogICAnc2NyZWVuc2hvdCcsIC8vIFNhZmFyaVxuICAgKiAgIC8vIFN5bWJvbHNcbiAgICogICAnQEB0b1N0cmluZ1RhZycsIC8vIENocm9tZTogXCJPYmplY3RcIiwgU2FmYXJpOiBcIkNvbnNvbGVcIlxuICAgKiAgIC8vIEEgdmFyaWV0eSBvZiBvdGhlciBzeW1ib2xzIGFsc28gc2VlbiBvbiBOb2RlXG4gICAqIF0pO1xuICAgKi9cblxuICAvLyAvLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vL1xuXG4gIC8qKiBAdHlwZSB7TWFrZUxvZ2dpbmdDb25zb2xlS2l0fSAqL1xuICBjb25zdCBtYWtlTG9nZ2luZ0NvbnNvbGVLaXQgPSAoKSA9PiB7XG4gICAgLy8gTm90IGZyb3plbiFcbiAgICBsZXQgbG9nQXJyYXkgPSBbXTtcblxuICAgIGNvbnN0IGxvZ2dpbmdDb25zb2xlID0gZnJvbUVudHJpZXMoXG4gICAgICBjb25zb2xlV2hpdGVsaXN0Lm1hcCgoW25hbWUsIF9dKSA9PiB7XG4gICAgICAgIC8vIFVzZSBhbiBhcnJvdyBmdW5jdGlvbiBzbyB0aGF0IGl0IGRvZXNuJ3QgY29tZSB3aXRoIGl0cyBvd24gbmFtZSBpblxuICAgICAgICAvLyBpdHMgcHJpbnRlZCBmb3JtLiBJbnN0ZWFkLCB3ZSdyZSBob3BpbmcgdGhhdCB0b29saW5nIHVzZXMgb25seVxuICAgICAgICAvLyB0aGUgYC5uYW1lYCBwcm9wZXJ0eSBzZXQgYmVsb3cuXG4gICAgICAgIC8qKlxuICAgICAgICAgKiBAcGFyYW0gey4uLmFueX0gYXJnc1xuICAgICAgICAgKi9cbiAgICAgICAgY29uc3QgbWV0aG9kID0gKC4uLmFyZ3MpID0+IHtcbiAgICAgICAgICBsb2dBcnJheS5wdXNoKFtuYW1lLCAuLi5hcmdzXSk7XG4gICAgICAgIH07XG4gICAgICAgIGRlZmluZVByb3BlcnR5KG1ldGhvZCwgJ25hbWUnLCB7IHZhbHVlOiBuYW1lIH0pO1xuICAgICAgICByZXR1cm4gW25hbWUsIGZyZWV6ZShtZXRob2QpXTtcbiAgICAgIH0pLFxuICAgICk7XG4gICAgZnJlZXplKGxvZ2dpbmdDb25zb2xlKTtcblxuICAgIGNvbnN0IHRha2VMb2cgPSAoKSA9PiB7XG4gICAgICBjb25zdCByZXN1bHQgPSBmcmVlemUobG9nQXJyYXkpO1xuICAgICAgbG9nQXJyYXkgPSBbXTtcbiAgICAgIHJldHVybiByZXN1bHQ7XG4gICAgfTtcbiAgICBmcmVlemUodGFrZUxvZyk7XG5cbiAgICBjb25zdCB0eXBlZExvZ2dpbmdDb25zb2xlID0gLyoqIEB0eXBlIHtWaXJ0dWFsQ29uc29sZX0gKi8gKGxvZ2dpbmdDb25zb2xlKTtcblxuICAgIHJldHVybiBmcmVlemUoeyBsb2dnaW5nQ29uc29sZTogdHlwZWRMb2dnaW5nQ29uc29sZSwgdGFrZUxvZyB9KTtcbiAgfTtcbiAgZnJlZXplKG1ha2VMb2dnaW5nQ29uc29sZUtpdCk7XG5cbiAgLy8gLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy9cblxuICAvKiogQHR5cGUge0Vycm9ySW5mb30gKi9cbiAgY29uc3QgRXJyb3JJbmZvID0ge1xuICAgIE5PVEU6ICdFUlJPUl9OT1RFOicsXG4gICAgTUVTU0FHRTogJ0VSUk9SX01FU1NBR0U6JyxcbiAgfTtcbiAgZnJlZXplKEVycm9ySW5mbyk7XG5cbiAgLyoqXG4gICAqIFRoZSBlcnJvciBhbm5vdGF0aW9ucyBhcmUgc2VudCB0byB0aGUgYmFzZUNvbnNvbGUgYnkgY2FsbGluZyBzb21lIGxldmVsXG4gICAqIG1ldGhvZC4gVGhlICdkZWJ1ZycgbGV2ZWwgc2VlbXMgYmVzdCwgYmVjYXVzZSB0aGUgQ2hyb21lIGNvbnNvbGUgY2xhc3NpZmllc1xuICAgKiBgZGVidWdgIGFzIHZlcmJvc2UgYW5kIGRvZXMgbm90IHNob3cgaXQgYnkgZGVmYXVsdC4gQnV0IHdlIGtlZXAgaXQgc3ltYm9saWNcbiAgICogc28gd2UgY2FuIGNoYW5nZSBvdXIgbWluZC4gKE9uIE5vZGUsIGBkZWJ1Z2AsIGBsb2dgLCBhbmQgYGluZm9gIGFyZSBhbGlhc2VzXG4gICAqIGZvciB0aGUgc2FtZSBmdW5jdGlvbiBhbmQgc28gd2lsbCBiZWhhdmUgdGhlIHNhbWUgdGhlcmUuKVxuICAgKi9cbiAgY29uc3QgQkFTRV9DT05TT0xFX0xFVkVMID0gJ2RlYnVnJztcblxuICAvKiogQHR5cGUge01ha2VDYXVzYWxDb25zb2xlfSAqL1xuICBjb25zdCBtYWtlQ2F1c2FsQ29uc29sZSA9IChiYXNlQ29uc29sZSwgbG9nZ2VkRXJyb3JIYW5kbGVyKSA9PiB7XG4gICAgY29uc3Qge1xuICAgICAgZ2V0U3RhY2tTdHJpbmcsXG4gICAgICB0YWtlTWVzc2FnZUxvZ0FyZ3MsXG4gICAgICB0YWtlTm90ZUxvZ0FyZ3NBcnJheSxcbiAgICB9ID0gbG9nZ2VkRXJyb3JIYW5kbGVyO1xuXG4gICAgLy8gYnkgXCJ0YWdnZWRcIiwgd2UgbWVhbiBmaXJzdCBzZW50IHRvIHRoZSBiYXNlQ29uc29sZSBhcyBhbiBhcmd1bWVudCBpbiBhXG4gICAgLy8gY29uc29sZSBsZXZlbCBtZXRob2QgY2FsbCwgaW4gd2hpY2ggaXQgaXMgc2hvd24gd2l0aCBhbiBpZGVudGlmeWluZyB0YWdcbiAgICAvLyBudW1iZXIuIFdlIG51bWJlciB0aGUgZXJyb3JzIGFjY29yZGluZyB0byB0aGUgb3JkZXIgaW5cbiAgICAvLyB3aGljaCB0aGV5IHdlcmUgZmlyc3QgbG9nZ2VkIHRvIHRoZSBiYXNlQ29uc29sZSwgc3RhcnRpbmcgYXQgMS5cbiAgICBsZXQgbnVtRXJyb3JzVGFnZ2VkID0gMDtcbiAgICAvKiogQHR5cGUgV2Vha01hcDxFcnJvciwgbnVtYmVyPiAqL1xuICAgIGNvbnN0IGVycm9yVGFnT3JkZXIgPSBuZXcgV2Vha01hcCgpO1xuXG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtFcnJvcn0gZXJyXG4gICAgICogQHJldHVybnMge3N0cmluZ31cbiAgICAgKi9cbiAgICBjb25zdCB0YWdFcnJvciA9IGVyciA9PiB7XG4gICAgICBsZXQgZXJyTnVtO1xuICAgICAgaWYgKGVycm9yVGFnT3JkZXIuaGFzKGVycikpIHtcbiAgICAgICAgZXJyTnVtID0gZXJyb3JUYWdPcmRlci5nZXQoZXJyKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG51bUVycm9yc1RhZ2dlZCArPSAxO1xuICAgICAgICBlcnJvclRhZ09yZGVyLnNldChlcnIsIG51bUVycm9yc1RhZ2dlZCk7XG4gICAgICAgIGVyck51bSA9IG51bUVycm9yc1RhZ2dlZDtcbiAgICAgIH1cbiAgICAgIHJldHVybiBgJHtlcnIubmFtZX0jJHtlcnJOdW19YDtcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtSZWFkb25seUFycmF5PGFueT59IGxvZ0FyZ3NcbiAgICAgKiBAcGFyYW0ge0FycmF5PGFueT59IHN1YkVycm9yc1NpbmtcbiAgICAgKiBAcmV0dXJucyB7YW55fVxuICAgICAqL1xuICAgIGNvbnN0IGV4dHJhY3RFcnJvckFyZ3MgPSAobG9nQXJncywgc3ViRXJyb3JzU2luaykgPT4ge1xuICAgICAgY29uc3QgYXJnVGFncyA9IGxvZ0FyZ3MubWFwKGFyZyA9PiB7XG4gICAgICAgIGlmIChhcmcgaW5zdGFuY2VvZiBFcnJvcikge1xuICAgICAgICAgIHN1YkVycm9yc1NpbmsucHVzaChhcmcpO1xuICAgICAgICAgIHJldHVybiBgKCR7dGFnRXJyb3IoYXJnKX0pYDtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gYXJnO1xuICAgICAgfSk7XG4gICAgICByZXR1cm4gYXJnVGFncztcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtFcnJvcn0gZXJyb3JcbiAgICAgKiBAcGFyYW0ge0Vycm9ySW5mb0tpbmR9IGtpbmRcbiAgICAgKiBAcGFyYW0ge3JlYWRvbmx5IGFueVtdfSBsb2dBcmdzXG4gICAgICogQHBhcmFtIHtBcnJheTxFcnJvcj59IHN1YkVycm9yc1NpbmtcbiAgICAgKi9cbiAgICBjb25zdCBsb2dFcnJvckluZm8gPSAoZXJyb3IsIGtpbmQsIGxvZ0FyZ3MsIHN1YkVycm9yc1NpbmspID0+IHtcbiAgICAgIGNvbnN0IGVycm9yVGFnID0gdGFnRXJyb3IoZXJyb3IpO1xuICAgICAgY29uc3QgZXJyb3JOYW1lID1cbiAgICAgICAga2luZCA9PT0gRXJyb3JJbmZvLk1FU1NBR0UgPyBgJHtlcnJvclRhZ306YCA6IGAke2Vycm9yVGFnfSAke2tpbmR9YDtcbiAgICAgIGNvbnN0IGFyZ1RhZ3MgPSBleHRyYWN0RXJyb3JBcmdzKGxvZ0FyZ3MsIHN1YkVycm9yc1NpbmspO1xuICAgICAgYmFzZUNvbnNvbGVbQkFTRV9DT05TT0xFX0xFVkVMXShlcnJvck5hbWUsIC4uLmFyZ1RhZ3MpO1xuICAgIH07XG5cbiAgICAvKipcbiAgICAgKiBMb2dzIHRoZSBgc3ViRXJyb3JzYCB3aXRoaW4gYSBncm91cCBuYW1lIG1lbnRpb25pbmcgYG9wdFRhZ2AuXG4gICAgICpcbiAgICAgKiBAcGFyYW0ge0Vycm9yW119IHN1YkVycm9yc1xuICAgICAqIEBwYXJhbSB7c3RyaW5nIHwgdW5kZWZpbmVkfSBvcHRUYWdcbiAgICAgKiBAcmV0dXJucyB7dm9pZH1cbiAgICAgKi9cbiAgICBjb25zdCBsb2dTdWJFcnJvcnMgPSAoc3ViRXJyb3JzLCBvcHRUYWcgPSB1bmRlZmluZWQpID0+IHtcbiAgICAgIGlmIChzdWJFcnJvcnMubGVuZ3RoID09PSAwKSB7XG4gICAgICAgIHJldHVybjtcbiAgICAgIH1cbiAgICAgIGlmIChzdWJFcnJvcnMubGVuZ3RoID09PSAxICYmIG9wdFRhZyA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby11c2UtYmVmb3JlLWRlZmluZVxuICAgICAgICBsb2dFcnJvcihzdWJFcnJvcnNbMF0pO1xuICAgICAgICByZXR1cm47XG4gICAgICB9XG4gICAgICBsZXQgbGFiZWw7XG4gICAgICBpZiAoc3ViRXJyb3JzLmxlbmd0aCA9PT0gMSkge1xuICAgICAgICBsYWJlbCA9IGBOZXN0ZWQgZXJyb3JgO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgbGFiZWwgPSBgTmVzdGVkICR7c3ViRXJyb3JzLmxlbmd0aH0gZXJyb3JzYDtcbiAgICAgIH1cbiAgICAgIGlmIChvcHRUYWcgIT09IHVuZGVmaW5lZCkge1xuICAgICAgICBsYWJlbCA9IGAke2xhYmVsfSB1bmRlciAke29wdFRhZ31gO1xuICAgICAgfVxuICAgICAgYmFzZUNvbnNvbGUuZ3JvdXAobGFiZWwpO1xuICAgICAgdHJ5IHtcbiAgICAgICAgZm9yIChjb25zdCBzdWJFcnJvciBvZiBzdWJFcnJvcnMpIHtcbiAgICAgICAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tdXNlLWJlZm9yZS1kZWZpbmVcbiAgICAgICAgICBsb2dFcnJvcihzdWJFcnJvcik7XG4gICAgICAgIH1cbiAgICAgIH0gZmluYWxseSB7XG4gICAgICAgIGJhc2VDb25zb2xlLmdyb3VwRW5kKCk7XG4gICAgICB9XG4gICAgfTtcblxuICAgIGNvbnN0IGVycm9yc0xvZ2dlZCA9IG5ldyBXZWFrU2V0KCk7XG5cbiAgICAvKiogQHR5cGUge05vdGVDYWxsYmFja30gKi9cbiAgICBjb25zdCBub3RlQ2FsbGJhY2sgPSAoZXJyb3IsIG5vdGVMb2dBcmdzKSA9PiB7XG4gICAgICBjb25zdCBzdWJFcnJvcnMgPSBbXTtcbiAgICAgIC8vIEFubm90YXRpb24gYXJyaXZlZCBhZnRlciB0aGUgZXJyb3IgaGFzIGFscmVhZHkgYmVlbiBsb2dnZWQsXG4gICAgICAvLyBzbyBqdXN0IGxvZyB0aGUgYW5ub3RhdGlvbiBpbW1lZGlhdGVseSwgcmF0aGVyIHRoYW4gcmVtZW1iZXJpbmcgaXQuXG4gICAgICBsb2dFcnJvckluZm8oZXJyb3IsIEVycm9ySW5mby5OT1RFLCBub3RlTG9nQXJncywgc3ViRXJyb3JzKTtcbiAgICAgIGxvZ1N1YkVycm9ycyhzdWJFcnJvcnMsIHRhZ0Vycm9yKGVycm9yKSk7XG4gICAgfTtcblxuICAgIC8qKlxuICAgICAqIEBwYXJhbSB7RXJyb3J9IGVycm9yXG4gICAgICovXG4gICAgY29uc3QgbG9nRXJyb3IgPSBlcnJvciA9PiB7XG4gICAgICBpZiAoZXJyb3JzTG9nZ2VkLmhhcyhlcnJvcikpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgICAgfVxuICAgICAgY29uc3QgZXJyb3JUYWcgPSB0YWdFcnJvcihlcnJvcik7XG4gICAgICBlcnJvcnNMb2dnZWQuYWRkKGVycm9yKTtcbiAgICAgIGNvbnN0IHN1YkVycm9ycyA9IFtdO1xuICAgICAgY29uc3QgbWVzc2FnZUxvZ0FyZ3MgPSB0YWtlTWVzc2FnZUxvZ0FyZ3MoZXJyb3IpO1xuICAgICAgY29uc3Qgbm90ZUxvZ0FyZ3NBcnJheSA9IHRha2VOb3RlTG9nQXJnc0FycmF5KGVycm9yLCBub3RlQ2FsbGJhY2spO1xuICAgICAgLy8gU2hvdyB0aGUgZXJyb3IncyBtb3N0IGluZm9ybWF0aXZlIGVycm9yIG1lc3NhZ2VcbiAgICAgIGlmIChtZXNzYWdlTG9nQXJncyA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICAgIC8vIElmIHRoZXJlIGlzIG5vIG1lc3NhZ2UgbG9nIGFyZ3MsIHRoZW4ganVzdCBzaG93IHRoZSBtZXNzYWdlIHRoYXRcbiAgICAgICAgLy8gdGhlIGVycm9yIGl0c2VsZiBjYXJyaWVzLlxuICAgICAgICBiYXNlQ29uc29sZVtCQVNFX0NPTlNPTEVfTEVWRUxdKGAke2Vycm9yVGFnfTpgLCBlcnJvci5tZXNzYWdlKTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIC8vIElmIHRoZXJlIGlzIG9uZSwgd2UgdGFrZSBpdCB0byBiZSBzdHJpY3RseSBtb3JlIGluZm9ybWF0aXZlIHRoYW4gdGhlXG4gICAgICAgIC8vIG1lc3NhZ2Ugc3RyaW5nIGNhcnJpZWQgYnkgdGhlIGVycm9yLCBzbyBzaG93IGl0ICppbnN0ZWFkKi5cbiAgICAgICAgbG9nRXJyb3JJbmZvKGVycm9yLCBFcnJvckluZm8uTUVTU0FHRSwgbWVzc2FnZUxvZ0FyZ3MsIHN1YkVycm9ycyk7XG4gICAgICB9XG4gICAgICAvLyBBZnRlciB0aGUgbWVzc2FnZSBidXQgYmVmb3JlIGFueSBvdGhlciBhbm5vdGF0aW9ucywgc2hvdyB0aGUgc3RhY2suXG4gICAgICBsZXQgc3RhY2tTdHJpbmcgPSBnZXRTdGFja1N0cmluZyhlcnJvcik7XG4gICAgICBpZiAoXG4gICAgICAgIHR5cGVvZiBzdGFja1N0cmluZyA9PT0gJ3N0cmluZycgJiZcbiAgICAgICAgc3RhY2tTdHJpbmcubGVuZ3RoID49IDEgJiZcbiAgICAgICAgIXN0YWNrU3RyaW5nLmVuZHNXaXRoKCdcXG4nKVxuICAgICAgKSB7XG4gICAgICAgIHN0YWNrU3RyaW5nICs9ICdcXG4nO1xuICAgICAgfVxuICAgICAgYmFzZUNvbnNvbGVbQkFTRV9DT05TT0xFX0xFVkVMXShzdGFja1N0cmluZyk7XG4gICAgICAvLyBTaG93IHRoZSBvdGhlciBhbm5vdGF0aW9ucyBvbiBlcnJvclxuICAgICAgZm9yIChjb25zdCBub3RlTG9nQXJncyBvZiBub3RlTG9nQXJnc0FycmF5KSB7XG4gICAgICAgIGxvZ0Vycm9ySW5mbyhlcnJvciwgRXJyb3JJbmZvLk5PVEUsIG5vdGVMb2dBcmdzLCBzdWJFcnJvcnMpO1xuICAgICAgfVxuICAgICAgLy8gZXhwbGFpbiBhbGwgdGhlIGVycm9ycyBzZWVuIGluIHRoZSBtZXNzYWdlcyBhbHJlYWR5IGVtaXR0ZWQuXG4gICAgICBsb2dTdWJFcnJvcnMoc3ViRXJyb3JzLCBlcnJvclRhZyk7XG4gICAgfTtcblxuICAgIGNvbnN0IGxldmVsTWV0aG9kcyA9IGNvbnNvbGVMZXZlbE1ldGhvZHMubWFwKChbbGV2ZWwsIF9dKSA9PiB7XG4gICAgICAvKipcbiAgICAgICAqIEBwYXJhbSB7Li4uYW55fSBsb2dBcmdzXG4gICAgICAgKi9cbiAgICAgIGNvbnN0IGxldmVsTWV0aG9kID0gKC4uLmxvZ0FyZ3MpID0+IHtcbiAgICAgICAgY29uc3Qgc3ViRXJyb3JzID0gW107XG4gICAgICAgIGNvbnN0IGFyZ1RhZ3MgPSBleHRyYWN0RXJyb3JBcmdzKGxvZ0FyZ3MsIHN1YkVycm9ycyk7XG4gICAgICAgIC8vIEB0cy1pZ25vcmVcbiAgICAgICAgYmFzZUNvbnNvbGVbbGV2ZWxdKC4uLmFyZ1RhZ3MpO1xuICAgICAgICBsb2dTdWJFcnJvcnMoc3ViRXJyb3JzKTtcbiAgICAgIH07XG4gICAgICBkZWZpbmVQcm9wZXJ0eShsZXZlbE1ldGhvZCwgJ25hbWUnLCB7IHZhbHVlOiBsZXZlbCB9KTtcbiAgICAgIHJldHVybiBbbGV2ZWwsIGZyZWV6ZShsZXZlbE1ldGhvZCldO1xuICAgIH0pO1xuICAgIGNvbnN0IG90aGVyTWV0aG9kTmFtZXMgPSBjb25zb2xlT3RoZXJNZXRob2RzLmZpbHRlcihcbiAgICAgIChbbmFtZSwgX10pID0+IG5hbWUgaW4gYmFzZUNvbnNvbGUsXG4gICAgKTtcbiAgICBjb25zdCBvdGhlck1ldGhvZHMgPSBvdGhlck1ldGhvZE5hbWVzLm1hcCgoW25hbWUsIF9dKSA9PiB7XG4gICAgICAvKipcbiAgICAgICAqIEBwYXJhbSB7Li4uYW55fSBhcmdzXG4gICAgICAgKi9cbiAgICAgIGNvbnN0IG90aGVyTWV0aG9kID0gKC4uLmFyZ3MpID0+IHtcbiAgICAgICAgLy8gQHRzLWlnbm9yZVxuICAgICAgICBiYXNlQ29uc29sZVtuYW1lXSguLi5hcmdzKTtcbiAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgIH07XG4gICAgICBkZWZpbmVQcm9wZXJ0eShvdGhlck1ldGhvZCwgJ25hbWUnLCB7IHZhbHVlOiBuYW1lIH0pO1xuICAgICAgcmV0dXJuIFtuYW1lLCBmcmVlemUob3RoZXJNZXRob2QpXTtcbiAgICB9KTtcblxuICAgIGNvbnN0IGNhdXNhbENvbnNvbGUgPSBmcm9tRW50cmllcyhbLi4ubGV2ZWxNZXRob2RzLCAuLi5vdGhlck1ldGhvZHNdKTtcbiAgICByZXR1cm4gZnJlZXplKGNhdXNhbENvbnNvbGUpO1xuICB9O1xuICBmcmVlemUobWFrZUNhdXNhbENvbnNvbGUpO1xuXG4gIC8vIC8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vLy8vXG5cbiAgLyoqIEB0eXBlIHtGaWx0ZXJDb25zb2xlfSAqL1xuICBjb25zdCBmaWx0ZXJDb25zb2xlID0gKGJhc2VDb25zb2xlLCBmaWx0ZXIsIF90b3BpYyA9IHVuZGVmaW5lZCkgPT4ge1xuICAgIC8vIFRPRE8gZG8gc29tZXRoaW5nIHdpdGggb3B0aW9uYWwgdG9waWMgc3RyaW5nXG4gICAgY29uc3Qgd2hpbGVsaXN0ID0gY29uc29sZVdoaXRlbGlzdC5maWx0ZXIoKFtuYW1lLCBfXSkgPT4gbmFtZSBpbiBiYXNlQ29uc29sZSk7XG4gICAgY29uc3QgbWV0aG9kcyA9IHdoaWxlbGlzdC5tYXAoKFtuYW1lLCBzZXZlcml0eV0pID0+IHtcbiAgICAgIC8qKlxuICAgICAgICogQHBhcmFtIHsuLi5hbnl9IGFyZ3NcbiAgICAgICAqL1xuICAgICAgY29uc3QgbWV0aG9kID0gKC4uLmFyZ3MpID0+IHtcbiAgICAgICAgaWYgKHNldmVyaXR5ID09PSB1bmRlZmluZWQgfHwgZmlsdGVyLmNhbkxvZyhzZXZlcml0eSkpIHtcbiAgICAgICAgICAvLyBAdHMtaWdub3JlXG4gICAgICAgICAgYmFzZUNvbnNvbGVbbmFtZV0oLi4uYXJncyk7XG4gICAgICAgIH1cbiAgICAgIH07XG4gICAgICByZXR1cm4gW25hbWUsIGZyZWV6ZShtZXRob2QpXTtcbiAgICB9KTtcbiAgICBjb25zdCBmaWx0ZXJpbmdDb25zb2xlID0gZnJvbUVudHJpZXMobWV0aG9kcyk7XG4gICAgcmV0dXJuIGZyZWV6ZShmaWx0ZXJpbmdDb25zb2xlKTtcbiAgfTtcbiAgZnJlZXplKGZpbHRlckNvbnNvbGUpO1xuXG4gIC8vIEB0cy1jaGVja1xuXG4gIGNvbnN0IG9yaWdpbmFsQ29uc29sZSA9IGNvbnNvbGU7XG5cbiAgLyoqXG4gICAqIFdyYXAgY29uc29sZSB1bmxlc3Mgc3VwcHJlc3NlZC5cbiAgICogQXQgdGhlIG1vbWVudCwgdGhlIGNvbnNvbGUgaXMgY29uc2lkZXJlZCBhIGhvc3QgcG93ZXIgaW4gdGhlIHN0YXJ0XG4gICAqIGNvbXBhcnRtZW50LCBhbmQgbm90IGEgcHJpbW9yZGlhbC4gSGVuY2UgaXQgaXMgYWJzZW50IGZyb20gdGhlIHdoaWxlbGlzdFxuICAgKiBhbmQgYnlwYXNzZXMgdGhlIGludHJpbnNpY3NDb2xsZWN0b3IuXG4gICAqXG4gICAqIEBwYXJhbSB7XCJzYWZlXCIgfCBcInVuc2FmZVwifSBjb25zb2xlVGFtaW5nXG4gICAqIEBwYXJhbSB7R2V0U3RhY2tTdHJpbmc9fSBvcHRHZXRTdGFja1N0cmluZ1xuICAgKi9cbiAgY29uc3QgdGFtZUNvbnNvbGUgPSAoXG4gICAgY29uc29sZVRhbWluZyA9ICdzYWZlJyxcbiAgICBvcHRHZXRTdGFja1N0cmluZyA9IHVuZGVmaW5lZCxcbiAgKSA9PiB7XG4gICAgaWYgKGNvbnNvbGVUYW1pbmcgIT09ICdzYWZlJyAmJiBjb25zb2xlVGFtaW5nICE9PSAndW5zYWZlJykge1xuICAgICAgdGhyb3cgbmV3IEVycm9yKGB1bnJlY29nbml6ZWQgY29uc29sZVRhbWluZyAke2NvbnNvbGVUYW1pbmd9YCk7XG4gICAgfVxuXG4gICAgaWYgKGNvbnNvbGVUYW1pbmcgPT09ICd1bnNhZmUnKSB7XG4gICAgICByZXR1cm4geyBjb25zb2xlOiBvcmlnaW5hbENvbnNvbGUgfTtcbiAgICB9XG4gICAgbGV0IGxvZ2dlZEVycm9ySGFuZGxlciQxO1xuICAgIGlmIChvcHRHZXRTdGFja1N0cmluZyA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICBsb2dnZWRFcnJvckhhbmRsZXIkMSA9IGxvZ2dlZEVycm9ySGFuZGxlcjtcbiAgICB9IGVsc2Uge1xuICAgICAgbG9nZ2VkRXJyb3JIYW5kbGVyJDEgPSB7XG4gICAgICAgIC4uLmxvZ2dlZEVycm9ySGFuZGxlcixcbiAgICAgICAgZ2V0U3RhY2tTdHJpbmc6IG9wdEdldFN0YWNrU3RyaW5nLFxuICAgICAgfTtcbiAgICB9XG4gICAgY29uc3QgY2F1c2FsQ29uc29sZSA9IG1ha2VDYXVzYWxDb25zb2xlKG9yaWdpbmFsQ29uc29sZSwgbG9nZ2VkRXJyb3JIYW5kbGVyJDEpO1xuICAgIHJldHVybiB7IGNvbnNvbGU6IGNhdXNhbENvbnNvbGUgfTtcbiAgfTtcblxuICAvLyBXaGl0ZWxpc3QgbmFtZXMgZnJvbSBodHRwczovL3Y4LmRldi9kb2NzL3N0YWNrLXRyYWNlLWFwaVxuICAvLyBXaGl0ZWxpc3Rpbmcgb25seSB0aGUgbmFtZXMgdXNlZCBieSBlcnJvci1zdGFjay1zaGltL3NyYy92OFN0YWNrRnJhbWVzXG4gIC8vIGNhbGxTaXRlVG9GcmFtZSB0byBzaGltIHRoZSBlcnJvciBzdGFjayBwcm9wb3NhbC5cbiAgY29uc3Qgc2FmZVY4Q2FsbFNpdGVNZXRob2ROYW1lcyA9IFtcbiAgICAvLyBzdXBwcmVzcyAnZ2V0VGhpcycgZGVmaW5pdGVseVxuICAgICdnZXRUeXBlTmFtZScsXG4gICAgLy8gc3VwcHJlc3MgJ2dldEZ1bmN0aW9uJyBkZWZpbml0ZWx5XG4gICAgJ2dldEZ1bmN0aW9uTmFtZScsXG4gICAgJ2dldE1ldGhvZE5hbWUnLFxuICAgICdnZXRGaWxlTmFtZScsXG4gICAgJ2dldExpbmVOdW1iZXInLFxuICAgICdnZXRDb2x1bW5OdW1iZXInLFxuICAgICdnZXRFdmFsT3JpZ2luJyxcbiAgICAnaXNUb3BsZXZlbCcsXG4gICAgJ2lzRXZhbCcsXG4gICAgJ2lzTmF0aXZlJyxcbiAgICAnaXNDb25zdHJ1Y3RvcicsXG4gICAgJ2lzQXN5bmMnLFxuICAgIC8vIHN1cHByZXNzICdpc1Byb21pc2VBbGwnIGZvciBub3dcbiAgICAvLyBzdXBwcmVzcyAnZ2V0UHJvbWlzZUluZGV4JyBmb3Igbm93XG5cbiAgICAvLyBBZGRpdGlvbmFsIG5hbWVzIGZvdW5kIGJ5IGV4cGVyaW1lbnQsIGFic2VudCBmcm9tXG4gICAgLy8gaHR0cHM6Ly92OC5kZXYvZG9jcy9zdGFjay10cmFjZS1hcGlcbiAgICAnZ2V0UG9zaXRpb24nLFxuICAgICdnZXRTY3JpcHROYW1lT3JTb3VyY2VVUkwnLFxuXG4gICAgJ3RvU3RyaW5nJywgLy8gVE9ETyByZXBsYWNlIHRvIHVzZSBvbmx5IHdoaXRlbGlzdGVkIGluZm9cbiAgXTtcblxuICAvLyBUT0RPIHRoaXMgaXMgYSByaWRpY3Vsb3VzbHkgZXhwZW5zaXZlIHdheSB0byBhdHRlbnVhdGUgY2FsbHNpdGVzLlxuICAvLyBCZWZvcmUgdGhhdCBtYXR0ZXJzLCB3ZSBzaG91bGQgc3dpdGNoIHRvIGEgcmVhc29uYWJsZSByZXByZXNlbnRhdGlvbi5cbiAgY29uc3Qgc2FmZVY4Q2FsbFNpdGVGYWNldCA9IGNhbGxTaXRlID0+IHtcbiAgICBjb25zdCBtZXRob2RFbnRyeSA9IG5hbWUgPT4gW25hbWUsICgpID0+IGNhbGxTaXRlW25hbWVdKCldO1xuICAgIGNvbnN0IG8gPSBmcm9tRW50cmllcyhzYWZlVjhDYWxsU2l0ZU1ldGhvZE5hbWVzLm1hcChtZXRob2RFbnRyeSkpO1xuICAgIHJldHVybiBPYmplY3QuY3JlYXRlKG8sIHt9KTtcbiAgfTtcblxuICBjb25zdCBzYWZlVjhTU1QgPSBzc3QgPT4gc3N0Lm1hcChzYWZlVjhDYWxsU2l0ZUZhY2V0KTtcblxuICAvLyBJZiBpdCBoYXMgYC9ub2RlX21vZHVsZXMvYCBhbnl3aGVyZSBpbiBpdCwgb24gTm9kZSBpdCBpcyBsaWtlbHlcbiAgLy8gdG8gYmUgYSBkZXBlbmRlbnQgcGFja2FnZSBvZiB0aGUgY3VycmVudCBwYWNrYWdlLCBhbmQgc28gdG9cbiAgLy8gYmUgYW4gaW5mcmFzdHJ1Y3R1cmUgZnJhbWUgdG8gYmUgZHJvcHBlZCBmcm9tIGNvbmNpc2Ugc3RhY2sgdHJhY2VzLlxuICBjb25zdCBGSUxFTkFNRV9OT0RFX0RFUEVOREVOVFNfQ0VOU09SID0gL1xcL25vZGVfbW9kdWxlc1xcLy87XG5cbiAgLy8gSWYgaXQgYmVnaW5zIHdpdGggYGludGVybmFsL2Agb3IgYG5vZGU6aW50ZXJuYWxgIHRoZW4gaXQgaXMgbGlrZWx5XG4gIC8vIHBhcnQgb2YgdGhlIG5vZGUgaW5mcnVzdHJ1Y3RyZSBpdHNlbGYsIHRvIGJlIGRyb3BwZWQgZnJvbSBjb25jaXNlXG4gIC8vIHN0YWNrIHRyYWNlcy5cbiAgY29uc3QgRklMRU5BTUVfTk9ERV9JTlRFUk5BTFNfQ0VOU09SID0gL14oPzpub2RlOik/aW50ZXJuYWxcXC8vO1xuXG4gIC8vIEZyYW1lcyB3aXRoaW4gdGhlIGBhc3NlcnQuanNgIHBhY2thZ2Ugc2hvdWxkIGJlIGRyb3BwZWQgZnJvbVxuICAvLyBjb25jaXNlIHN0YWNrIHRyYWNlcywgYXMgdGhlc2UgYXJlIGp1c3Qgc3RlcHMgdG93YXJkcyBjcmVhdGluZyB0aGVcbiAgLy8gZXJyb3Igb2JqZWN0IGluIHF1ZXN0aW9uLlxuICBjb25zdCBGSUxFTkFNRV9BU1NFUlRfQ0VOU09SID0gL1xcL3BhY2thZ2VzXFwvc2VzXFwvc3JjXFwvZXJyb3JcXC9hc3NlcnQuanMkLztcblxuICAvLyBGcmFtZXMgd2l0aGluIHRoZSBgZXZlbnR1YWwtc2VuZGAgc2hpbSBzaG91bGQgYmUgZHJvcHBlZCBzbyB0aGF0IGNvbmNpc2VcbiAgLy8gZGVlcCBzdGFja3Mgb21pdCB0aGUgaW50ZXJuYWxzIG9mIHRoZSBldmVudHVhbC1zZW5kaW5nIG1lY2hhbmlzbSBjYXVzaW5nXG4gIC8vIGFzeW5jaHJvbm91cyBtZXNzYWdlcyB0byBiZSBzZW50LlxuICAvLyBOb3RlIHRoYXQgdGhlIGV2ZW50dWFsLXNlbmQgcGFja2FnZSB3aWxsIG1vdmUgZnJvbSBhZ29yaWMtc2RrIHRvXG4gIC8vIEVuZG8sIHNvIHRoaXMgcnVsZSB3aWxsIGJlIG9mIGdlbmVyYWwgaW50ZXJlc3QuXG4gIGNvbnN0IEZJTEVOQU1FX0VWRU5UVUFMX1NFTkRfQ0VOU09SID0gL1xcL3BhY2thZ2VzXFwvZXZlbnR1YWwtc2VuZFxcL3NyY1xcLy87XG5cbiAgLy8gQW55IHN0YWNrIGZyYW1lIHdob3NlIGBmaWxlTmFtZWAgbWF0Y2hlcyBhbnkgb2YgdGhlc2UgY2Vuc29yIHBhdHRlcm5zXG4gIC8vIHdpbGwgYmUgb21pdHRlZCBmcm9tIGNvbmNpc2Ugc3RhY2tzLlxuICAvLyBUT0RPIEVuYWJsZSB1c2VycyB0byBjb25maWd1cmUgRklMRU5BTUVfQ0VOU09SUyB2aWEgYGxvY2tkb3duYCBvcHRpb25zLlxuICBjb25zdCBGSUxFTkFNRV9DRU5TT1JTID0gW1xuICAgIEZJTEVOQU1FX05PREVfREVQRU5ERU5UU19DRU5TT1IsXG4gICAgRklMRU5BTUVfTk9ERV9JTlRFUk5BTFNfQ0VOU09SLFxuICAgIEZJTEVOQU1FX0FTU0VSVF9DRU5TT1IsXG4gICAgRklMRU5BTUVfRVZFTlRVQUxfU0VORF9DRU5TT1IsXG4gIF07XG5cbiAgLy8gU2hvdWxkIGEgc3RhY2sgZnJhbWUgd2l0aCB0aGlzIGFzIGl0cyBmaWxlTmFtZSBiZSBpbmNsdWRlZCBpbiBhIGNvbmNpc2VcbiAgLy8gc3RhY2sgdHJhY2U/XG4gIC8vIEV4cG9ydGVkIG9ubHkgc28gaXQgY2FuIGJlIHVuaXQgdGVzdGVkLlxuICAvLyBUT0RPIE1vdmUgc28gdGhhdCBpdCBhcHBsaWVzIG5vdCBqdXN0IHRvIHY4LlxuICBjb25zdCBmaWx0ZXJGaWxlTmFtZSA9IGZpbGVOYW1lID0+IHtcbiAgICBpZiAoIWZpbGVOYW1lKSB7XG4gICAgICAvLyBTdGFjayBmcmFtZXMgd2l0aCBubyBmaWxlTmFtZSBzaG91bGQgYXBwZWFyIGluIGNvbmNpc2Ugc3RhY2sgdHJhY2VzLlxuICAgICAgcmV0dXJuIHRydWU7XG4gICAgfVxuICAgIGZvciAoY29uc3QgZmlsdGVyIG9mIEZJTEVOQU1FX0NFTlNPUlMpIHtcbiAgICAgIGlmIChmaWx0ZXIudGVzdChmaWxlTmFtZSkpIHtcbiAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gdHJ1ZTtcbiAgfTtcblxuICAvLyBUaGUgYWQtaG9jIHJ1bGUgb2YgdGhlIGN1cnJlbnQgcGF0dGVybiBpcyB0aGF0IGFueSBsaWtlbHktZmlsZS1wYXRoIG9yXG4gIC8vIGxpa2VseSB1cmwtcGF0aCBwcmVmaXgsIGVuZGluZyBpbiBhIGAvLi4uL2Agc2hvdWxkIGdldCBkcm9wcGVkLlxuICAvLyBBbnl0aGluZyB0byB0aGUgbGVmdCBvZiB0aGUgbGlrZWx5IHBhdGggdGV4dCBpcyBrZXB0LlxuICAvLyBFdmVyeXRoaW5nIHRvIHRoZSByaWdodCBvZiBgLy4uLi9gIGlzIGtlcHQuIFRodXNcbiAgLy8gYCdPYmplY3QuYmFyICgvdmF0LXYxLy4uLi9ldmVudHVhbC1zZW5kL3Rlc3QvdGVzdC1kZWVwLXNlbmQuanM6MTM6MjEpJ2BcbiAgLy8gc2ltcGxpZmllcyB0b1xuICAvLyBgJ09iamVjdC5iYXIgKGV2ZW50dWFsLXNlbmQvdGVzdC90ZXN0LWRlZXAtc2VuZC5qczoxMzoyMSknYC5cbiAgLy9cbiAgLy8gU2VlIHRocmVhZCBzdGFydGluZyBhdFxuICAvLyBodHRwczovL2dpdGh1Yi5jb20vQWdvcmljL2Fnb3JpYy1zZGsvaXNzdWVzLzIzMjYjaXNzdWVjb21tZW50LTc3MzAyMDM4OVxuICBjb25zdCBDQUxMU0lURV9FTExJUFNFU19QQVRURVJOID0gL14oKD86LipbKCBdKT8pWzovXFx3Xy1dKlxcL1xcLlxcLlxcLlxcLyguKykkLztcblxuICAvLyBUaGUgYWQtaG9jIHJ1bGUgb2YgdGhlIGN1cnJlbnQgcGF0dGVybiBpcyB0aGF0IGFueSBsaWtlbHktZmlsZS1wYXRoIG9yXG4gIC8vIGxpa2VseSB1cmwtcGF0aCBwcmVmaXgsIGVuZGluZyBpbiBhIGAvYCBhbmQgcHJpb3IgdG8gYHBhY2thZ2UvYCBzaG91bGQgZ2V0XG4gIC8vIGRyb3BwZWQuXG4gIC8vIEFueXRoaW5nIHRvIHRoZSBsZWZ0IG9mIHRoZSBsaWtlbHkgcGF0aCBwcmVmaXggdGV4dCBpcyBrZXB0LiBgcGFja2FnZS9gIGFuZFxuICAvLyBldmVyeXRoaW5nIHRvIGl0cyByaWdodCBpcyBrZXB0LiBUaHVzXG4gIC8vIGAnT2JqZWN0LmJhciAoL1VzZXJzL21hcmttaWxsZXIvc3JjL29uZ2l0aHViL2Fnb3JpYy9hZ29yaWMtc2RrL3BhY2thZ2VzL2V2ZW50dWFsLXNlbmQvdGVzdC90ZXN0LWRlZXAtc2VuZC5qczoxMzoyMSknYFxuICAvLyBzaW1wbGlmaWVzIHRvXG4gIC8vIGAnT2JqZWN0LmJhciAocGFja2FnZXMvZXZlbnR1YWwtc2VuZC90ZXN0L3Rlc3QtZGVlcC1zZW5kLmpzOjEzOjIxKSdgLlxuICAvLyBOb3RlIHRoYXQgYC9wYWNrYWdlcy9gIGlzIGEgY29udmVudGlvbiBmb3IgbW9ub3JlcG9zIGVuY291cmFnZWQgYnlcbiAgLy8gbGVybmEuXG4gIGNvbnN0IENBTExTSVRFX1BBQ0tBR0VTX1BBVFRFUk4gPSAvXigoPzouKlsoIF0pPylbOi9cXHdfLV0qXFwvKHBhY2thZ2VzXFwvLispJC87XG5cbiAgLy8gVGhlIHVzZSBvZiB0aGVzZSBjYWxsU2l0ZSBwYXR0ZXJucyBiZWxvdyBhc3N1bWVzIHRoYXQgYW55IG1hdGNoIHdpbGwgYmluZFxuICAvLyBjYXB0dXJlIGdyb3VwcyBjb250YWluaW5nIHRoZSBwYXJ0cyBvZiB0aGUgb3JpZ2luYWwgc3RyaW5nIHdlIHdhbnRcbiAgLy8gdG8ga2VlcC4gVGhlIHBhcnRzIG91dHNpZGUgdGhvc2UgY2FwdHVyZSBncm91cHMgd2lsbCBiZSBkcm9wcGVkIGZyb20gY29uY2lzZVxuICAvLyBzdGFja3MuXG4gIC8vIFRPRE8gRW5hYmxlIHVzZXJzIHRvIGNvbmZpZ3VyZSBDQUxMU0lURV9QQVRURVJOUyB2aWEgYGxvY2tkb3duYCBvcHRpb25zLlxuICBjb25zdCBDQUxMU0lURV9QQVRURVJOUyA9IFtcbiAgICBDQUxMU0lURV9FTExJUFNFU19QQVRURVJOLFxuICAgIENBTExTSVRFX1BBQ0tBR0VTX1BBVFRFUk4sXG4gIF07XG5cbiAgLy8gRm9yIGEgc3RhY2sgZnJhbWUgdGhhdCBzaG91bGQgYmUgaW5jbHVkZWQgaW4gYSBjb25jaXNlIHN0YWNrIHRyYWNlLCBpZlxuICAvLyBgY2FsbFNpdGVTdHJpbmdgIGlzIHRoZSBvcmlnaW5hbCBzdHJpbmdpZmllZCBzdGFjayBmcmFtZSwgcmV0dXJuIHRoZVxuICAvLyBwb3NzaWJseS1zaG9ydGVyIHN0cmluZ2lmaWVkIHN0YWNrIGZyYW1lIHRoYXQgc2hvdWxkIGJlIHNob3duIGluc3RlYWQuXG4gIC8vIEV4cG9ydGVkIG9ubHkgc28gaXQgY2FuIGJlIHVuaXQgdGVzdGVkLlxuICAvLyBUT0RPIE1vdmUgc28gdGhhdCBpdCBhcHBsaWVzIG5vdCBqdXN0IHRvIHY4LlxuICBjb25zdCBzaG9ydGVuQ2FsbFNpdGVTdHJpbmcgPSBjYWxsU2l0ZVN0cmluZyA9PiB7XG4gICAgZm9yIChjb25zdCBmaWx0ZXIgb2YgQ0FMTFNJVEVfUEFUVEVSTlMpIHtcbiAgICAgIGNvbnN0IG1hdGNoID0gZmlsdGVyLmV4ZWMoY2FsbFNpdGVTdHJpbmcpO1xuICAgICAgaWYgKG1hdGNoKSB7XG4gICAgICAgIHJldHVybiBtYXRjaC5zbGljZSgxKS5qb2luKCcnKTtcbiAgICAgIH1cbiAgICB9XG4gICAgcmV0dXJuIGNhbGxTaXRlU3RyaW5nO1xuICB9O1xuXG4gIGZ1bmN0aW9uIHRhbWVWOEVycm9yQ29uc3RydWN0b3IoXG4gICAgT3JpZ2luYWxFcnJvcixcbiAgICBJbml0aWFsRXJyb3IsXG4gICAgZXJyb3JUYW1pbmcsXG4gICAgc3RhY2tGaWx0ZXJpbmcsXG4gICkge1xuICAgIC8vIGNvbnN0IGNhbGxTaXRlRmlsdGVyID0gX2NhbGxTaXRlID0+IHRydWU7XG4gICAgY29uc3QgY2FsbFNpdGVGaWx0ZXIgPSBjYWxsU2l0ZSA9PiB7XG4gICAgICBpZiAoc3RhY2tGaWx0ZXJpbmcgPT09ICd2ZXJib3NlJykge1xuICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBmaWx0ZXJGaWxlTmFtZShjYWxsU2l0ZS5nZXRGaWxlTmFtZSgpKTtcbiAgICB9O1xuXG4gICAgY29uc3QgY2FsbFNpdGVTdHJpbmdpZmllciA9IGNhbGxTaXRlID0+IHtcbiAgICAgIGxldCBjYWxsU2l0ZVN0cmluZyA9IGAke2NhbGxTaXRlfWA7XG4gICAgICBpZiAoc3RhY2tGaWx0ZXJpbmcgPT09ICdjb25jaXNlJykge1xuICAgICAgICBjYWxsU2l0ZVN0cmluZyA9IHNob3J0ZW5DYWxsU2l0ZVN0cmluZyhjYWxsU2l0ZVN0cmluZyk7XG4gICAgICB9XG4gICAgICByZXR1cm4gYFxcbiAgYXQgJHtjYWxsU2l0ZVN0cmluZ31gO1xuICAgIH07XG5cbiAgICBjb25zdCBzdGFja1N0cmluZ0Zyb21TU1QgPSAoX2Vycm9yLCBzc3QpID0+XG4gICAgICBbLi4uc3N0LmZpbHRlcihjYWxsU2l0ZUZpbHRlcikubWFwKGNhbGxTaXRlU3RyaW5naWZpZXIpXS5qb2luKCcnKTtcblxuICAgIC8vIE1hcHBpbmcgZnJvbSBlcnJvciBpbnN0YW5jZSB0byB0aGUgc3RydWN0dXJlZCBzdGFjayB0cmFjZSBjYXB0dXJpbmcgdGhlXG4gICAgLy8gc3RhY2sgZm9yIHRoYXQgaW5zdGFuY2UuXG4gICAgY29uc3Qgc3N0cyA9IG5ldyBXZWFrTWFwKCk7XG5cbiAgICAvLyBVc2UgY29uY2lzZSBtZXRob2RzIHRvIG9idGFpbiBuYW1lZCBmdW5jdGlvbnMgd2l0aG91dCBjb25zdHJ1Y3RvcnMuXG4gICAgY29uc3QgdGFtZWRNZXRob2RzID0ge1xuICAgICAgLy8gVGhlIG9wdGlvbmFsIGBvcHRGbmAgYXJndW1lbnQgaXMgZm9yIGN1dHRpbmcgb2ZmIHRoZSBib3R0b20gb2ZcbiAgICAgIC8vIHRoZSBzdGFjayAtLS0gZm9yIGNhcHR1cmluZyB0aGUgc3RhY2sgb25seSBhYm92ZSB0aGUgdG9wbW9zdFxuICAgICAgLy8gY2FsbCB0byB0aGF0IGZ1bmN0aW9uLiBTaW5jZSB0aGlzIGlzbid0IHRoZSBcInJlYWxcIiBjYXB0dXJlU3RhY2tUcmFjZVxuICAgICAgLy8gYnV0IGluc3RlYWQgY2FsbHMgdGhlIHJlYWwgb25lLCBpZiBubyBvdGhlciBjdXRvZmYgaXMgcHJvdmlkZWQsXG4gICAgICAvLyB3ZSBjdXQgdGhpcyBvbmUgb2ZmLlxuICAgICAgY2FwdHVyZVN0YWNrVHJhY2UoZXJyb3IsIG9wdEZuID0gdGFtZWRNZXRob2RzLmNhcHR1cmVTdGFja1RyYWNlKSB7XG4gICAgICAgIGlmICh0eXBlb2YgT3JpZ2luYWxFcnJvci5jYXB0dXJlU3RhY2tUcmFjZSA9PT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICAgIC8vIE9yaWdpbmFsRXJyb3IuY2FwdHVyZVN0YWNrVHJhY2UgaXMgb25seSBvbiB2OFxuICAgICAgICAgIE9yaWdpbmFsRXJyb3IuY2FwdHVyZVN0YWNrVHJhY2UoZXJyb3IsIG9wdEZuKTtcbiAgICAgICAgICByZXR1cm47XG4gICAgICAgIH1cbiAgICAgICAgUmVmbGVjdC5zZXQoZXJyb3IsICdzdGFjaycsICcnKTtcbiAgICAgIH0sXG4gICAgICAvLyBTaGltIG9mIHByb3Bvc2VkIHNwZWNpYWwgcG93ZXIsIHRvIHJlc2lkZSBieSBkZWZhdWx0IG9ubHlcbiAgICAgIC8vIGluIHRoZSBzdGFydCBjb21wYXJ0bWVudCwgZm9yIGdldHRpbmcgdGhlIHN0YWNrIHRyYWNlYmFja1xuICAgICAgLy8gc3RyaW5nIGFzc29jaWF0ZWQgd2l0aCBhbiBlcnJvci5cbiAgICAgIC8vIFNlZSBodHRwczovL3RjMzkuZXMvcHJvcG9zYWwtZXJyb3Itc3RhY2tzL1xuICAgICAgZ2V0U3RhY2tTdHJpbmcoZXJyb3IpIHtcbiAgICAgICAgaWYgKCFzc3RzLmhhcyhlcnJvcikpIHtcbiAgICAgICAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tdm9pZFxuICAgICAgICAgIHZvaWQgZXJyb3Iuc3RhY2s7XG4gICAgICAgIH1cbiAgICAgICAgY29uc3Qgc3N0ID0gc3N0cy5nZXQoZXJyb3IpO1xuICAgICAgICBpZiAoIXNzdCkge1xuICAgICAgICAgIHJldHVybiAnJztcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gc3RhY2tTdHJpbmdGcm9tU1NUKGVycm9yLCBzc3QpO1xuICAgICAgfSxcbiAgICAgIHByZXBhcmVTdGFja1RyYWNlKGVycm9yLCBzc3QpIHtcbiAgICAgICAgc3N0cy5zZXQoZXJyb3IsIHNzdCk7XG4gICAgICAgIGlmIChlcnJvclRhbWluZyA9PT0gJ3Vuc2FmZScpIHtcbiAgICAgICAgICBjb25zdCBzdGFja1N0cmluZyA9IHN0YWNrU3RyaW5nRnJvbVNTVChlcnJvciwgc3N0KTtcbiAgICAgICAgICByZXR1cm4gYCR7ZXJyb3J9JHtzdGFja1N0cmluZ31gO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiAnJztcbiAgICAgIH0sXG4gICAgfTtcblxuICAgIC8vIEEgcHJlcGFyZUZuIGlzIGEgcHJlcGFyZVN0YWNrVHJhY2UgZnVuY3Rpb24uXG4gICAgLy8gQW4gc3N0IGlzIGEgYHN0cnVjdHVyZWRTdGFja1RyYWNlYCwgd2hpY2ggaXMgYW4gYXJyYXkgb2ZcbiAgICAvLyBjYWxsc2l0ZXMuXG4gICAgLy8gQSB1c2VyIHByZXBhcmVGbiBpcyBhIHByZXBhcmVGbiBkZWZpbmVkIGJ5IGEgY2xpZW50IG9mIHRoaXMgQVBJLFxuICAgIC8vIGFuZCBwcm92aWRlZCBieSBhc3NpZ25pbmcgdG8gYEVycm9yLnByZXBhcmVTdGFja1RyYWNlYC5cbiAgICAvLyBBIHVzZXIgcHJlcGFyZUZuIHNob3VsZCBvbmx5IHJlY2VpdmUgYW4gYXR0ZW51YXRlZCBzc3QsIHdoaWNoXG4gICAgLy8gaXMgYW4gYXJyYXkgb2YgYXR0ZW51YXRlZCBjYWxsc2l0ZXMuXG4gICAgLy8gQSBzeXN0ZW0gcHJlcGFyZUZuIGlzIHRoZSBwcmVwYXJlRm4gY3JlYXRlZCBieSB0aGlzIG1vZHVsZSB0b1xuICAgIC8vIGJlIGluc3RhbGxlZCBvbiB0aGUgcmVhbCBgRXJyb3JgIGNvbnN0cnVjdG9yLCB0byByZWNlaXZlXG4gICAgLy8gYW4gb3JpZ2luYWwgc3N0LCBpLmUuLCBhbiBhcnJheSBvZiB1bmF0dGVudWF0ZWQgY2FsbHNpdGVzLlxuICAgIC8vIEFuIGlucHV0IHByZXBhcmVGbiBpcyBhIGZ1bmN0aW9uIHRoZSB1c2VyIGFzc2lnbnMgdG9cbiAgICAvLyBgRXJyb3IucHJlcGFyZVN0YWNrVHJhY2VgLCB3aGljaCBtaWdodCBiZSBhIHVzZXIgcHJlcGFyZUZuIG9yXG4gICAgLy8gYSBzeXN0ZW0gcHJlcGFyZUZuIHByZXZpb3VzbHkgb2J0YWluZWQgYnkgcmVhZGluZ1xuICAgIC8vIGBFcnJvci5wcmVwYXJlU3RhY2tUcmFjZWAuXG5cbiAgICBjb25zdCBkZWZhdWx0UHJlcGFyZUZuID0gdGFtZWRNZXRob2RzLnByZXBhcmVTdGFja1RyYWNlO1xuXG4gICAgT3JpZ2luYWxFcnJvci5wcmVwYXJlU3RhY2tUcmFjZSA9IGRlZmF1bHRQcmVwYXJlRm47XG5cbiAgICAvLyBBIHdlYWtzZXQgYnJhbmRpbmcgc29tZSBmdW5jdGlvbnMgYXMgc3lzdGVtIHByZXBhcmVGbnMsIGFsbCBvZiB3aGljaFxuICAgIC8vIG11c3QgYmUgZGVmaW5lZCBieSB0aGlzIG1vZHVsZSwgc2luY2UgdGhleSBjYW4gcmVjZWl2ZSBhblxuICAgIC8vIHVuYXR0ZW51YXRlZCBzc3QuXG4gICAgY29uc3Qgc3lzdGVtUHJlcGFyZUZuU2V0ID0gbmV3IFdlYWtTZXQoW2RlZmF1bHRQcmVwYXJlRm5dKTtcblxuICAgIGNvbnN0IHN5c3RlbVByZXBhcmVGbkZvciA9IGlucHV0UHJlcGFyZUZuID0+IHtcbiAgICAgIGlmIChzeXN0ZW1QcmVwYXJlRm5TZXQuaGFzKGlucHV0UHJlcGFyZUZuKSkge1xuICAgICAgICByZXR1cm4gaW5wdXRQcmVwYXJlRm47XG4gICAgICB9XG4gICAgICAvLyBVc2UgY29uY2lzZSBtZXRob2RzIHRvIG9idGFpbiBuYW1lZCBmdW5jdGlvbnMgd2l0aG91dCBjb25zdHJ1Y3RvcnMuXG4gICAgICBjb25zdCBzeXN0ZW1NZXRob2RzID0ge1xuICAgICAgICBwcmVwYXJlU3RhY2tUcmFjZShlcnJvciwgc3N0KSB7XG4gICAgICAgICAgc3N0cy5zZXQoZXJyb3IsIHNzdCk7XG4gICAgICAgICAgcmV0dXJuIGlucHV0UHJlcGFyZUZuKGVycm9yLCBzYWZlVjhTU1Qoc3N0KSk7XG4gICAgICAgIH0sXG4gICAgICB9O1xuICAgICAgc3lzdGVtUHJlcGFyZUZuU2V0LmFkZChzeXN0ZW1NZXRob2RzLnByZXBhcmVTdGFja1RyYWNlKTtcbiAgICAgIHJldHVybiBzeXN0ZW1NZXRob2RzLnByZXBhcmVTdGFja1RyYWNlO1xuICAgIH07XG5cbiAgICAvLyBOb3RlIGBzdGFja1RyYWNlTGltaXRgIGFjY2Vzc29yIGFscmVhZHkgZGVmaW5lZCBieVxuICAgIC8vIHRhbWUtZXJyb3ItY29uc3RydWN0b3IuanNcbiAgICBkZWZpbmVQcm9wZXJ0aWVzKEluaXRpYWxFcnJvciwge1xuICAgICAgY2FwdHVyZVN0YWNrVHJhY2U6IHtcbiAgICAgICAgdmFsdWU6IHRhbWVkTWV0aG9kcy5jYXB0dXJlU3RhY2tUcmFjZSxcbiAgICAgICAgd3JpdGFibGU6IHRydWUsXG4gICAgICAgIGVudW1lcmFibGU6IGZhbHNlLFxuICAgICAgICBjb25maWd1cmFibGU6IHRydWUsXG4gICAgICB9LFxuICAgICAgcHJlcGFyZVN0YWNrVHJhY2U6IHtcbiAgICAgICAgZ2V0KCkge1xuICAgICAgICAgIHJldHVybiBPcmlnaW5hbEVycm9yLnByZXBhcmVTdGFja1RyYWNlO1xuICAgICAgICB9LFxuICAgICAgICBzZXQoaW5wdXRQcmVwYXJlU3RhY2tUcmFjZUZuKSB7XG4gICAgICAgICAgaWYgKHR5cGVvZiBpbnB1dFByZXBhcmVTdGFja1RyYWNlRm4gPT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICAgIGNvbnN0IHN5c3RlbVByZXBhcmVGbiA9IHN5c3RlbVByZXBhcmVGbkZvcihpbnB1dFByZXBhcmVTdGFja1RyYWNlRm4pO1xuICAgICAgICAgICAgT3JpZ2luYWxFcnJvci5wcmVwYXJlU3RhY2tUcmFjZSA9IHN5c3RlbVByZXBhcmVGbjtcbiAgICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgICAgT3JpZ2luYWxFcnJvci5wcmVwYXJlU3RhY2tUcmFjZSA9IGRlZmF1bHRQcmVwYXJlRm47XG4gICAgICAgICAgfVxuICAgICAgICB9LFxuICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlLFxuICAgICAgfSxcbiAgICB9KTtcblxuICAgIHJldHVybiB0YW1lZE1ldGhvZHMuZ2V0U3RhY2tTdHJpbmc7XG4gIH1cblxuICAvLyBQcmVzZW50IG9uIGF0IGxlYXN0IEZGLiBQcm9wb3NlZCBieSBFcnJvci1wcm9wb3NhbC4gTm90IG9uIFNFUyB3aGl0ZWxpc3RcbiAgLy8gc28gZ3JhYiBpdCBiZWZvcmUgaXQgaXMgcmVtb3ZlZC5cbiAgY29uc3Qgc3RhY2tEZXNjID0gZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKEVycm9yLnByb3RvdHlwZSwgJ3N0YWNrJyk7XG4gIGNvbnN0IHN0YWNrR2V0dGVyID0gc3RhY2tEZXNjICYmIHN0YWNrRGVzYy5nZXQ7XG5cbiAgLy8gVXNlIGNvbmNpc2UgbWV0aG9kcyB0byBvYnRhaW4gbmFtZWQgZnVuY3Rpb25zIHdpdGhvdXQgY29uc3RydWN0b3JzLlxuICBjb25zdCB0YW1lZE1ldGhvZHMkMSA9IHtcbiAgICBnZXRTdGFja1N0cmluZyhlcnJvcikge1xuICAgICAgaWYgKHR5cGVvZiBzdGFja0dldHRlciA9PT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICByZXR1cm4gYXBwbHkoc3RhY2tHZXR0ZXIsIGVycm9yLCBbXSk7XG4gICAgICB9IGVsc2UgaWYgKCdzdGFjaycgaW4gZXJyb3IpIHtcbiAgICAgICAgLy8gVGhlIGZhbGxiYWNrIGlzIHRvIGp1c3QgdXNlIHRoZSBkZSBmYWN0byBgZXJyb3Iuc3RhY2tgIGlmIHByZXNlbnRcbiAgICAgICAgcmV0dXJuIGAke2Vycm9yLnN0YWNrfWA7XG4gICAgICB9XG4gICAgICByZXR1cm4gJyc7XG4gICAgfSxcbiAgfTtcblxuICBmdW5jdGlvbiB0YW1lRXJyb3JDb25zdHJ1Y3RvcihcbiAgICBlcnJvclRhbWluZyA9ICdzYWZlJyxcbiAgICBzdGFja0ZpbHRlcmluZyA9ICdjb25jaXNlJyxcbiAgKSB7XG4gICAgaWYgKGVycm9yVGFtaW5nICE9PSAnc2FmZScgJiYgZXJyb3JUYW1pbmcgIT09ICd1bnNhZmUnKSB7XG4gICAgICB0aHJvdyBuZXcgRXJyb3IoYHVucmVjb2duaXplZCBlcnJvclRhbWluZyAke2Vycm9yVGFtaW5nfWApO1xuICAgIH1cbiAgICBpZiAoc3RhY2tGaWx0ZXJpbmcgIT09ICdjb25jaXNlJyAmJiBzdGFja0ZpbHRlcmluZyAhPT0gJ3ZlcmJvc2UnKSB7XG4gICAgICB0aHJvdyBuZXcgRXJyb3IoYHVucmVjb2duaXplZCBzdGFja0ZpbHRlcmluZyAke3N0YWNrRmlsdGVyaW5nfWApO1xuICAgIH1cbiAgICBjb25zdCBPcmlnaW5hbEVycm9yID0gRXJyb3I7XG4gICAgY29uc3QgRXJyb3JQcm90b3R5cGUgPSBPcmlnaW5hbEVycm9yLnByb3RvdHlwZTtcblxuICAgIGNvbnN0IHBsYXRmb3JtID1cbiAgICAgIHR5cGVvZiBPcmlnaW5hbEVycm9yLmNhcHR1cmVTdGFja1RyYWNlID09PSAnZnVuY3Rpb24nID8gJ3Y4JyA6ICd1bmtub3duJztcblxuICAgIGNvbnN0IG1ha2VFcnJvckNvbnN0cnVjdG9yID0gKF8gPSB7fSkgPT4ge1xuICAgICAgY29uc3QgUmVzdWx0RXJyb3IgPSBmdW5jdGlvbiBFcnJvciguLi5yZXN0KSB7XG4gICAgICAgIGxldCBlcnJvcjtcbiAgICAgICAgaWYgKG5ldy50YXJnZXQgPT09IHVuZGVmaW5lZCkge1xuICAgICAgICAgIGVycm9yID0gYXBwbHkoT3JpZ2luYWxFcnJvciwgdGhpcywgcmVzdCk7XG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgZXJyb3IgPSBjb25zdHJ1Y3QoT3JpZ2luYWxFcnJvciwgcmVzdCwgbmV3LnRhcmdldCk7XG4gICAgICAgIH1cbiAgICAgICAgaWYgKHBsYXRmb3JtID09PSAndjgnKSB7XG4gICAgICAgICAgLy8gVE9ETyBMaWtlbHkgZXhwZW5zaXZlIVxuICAgICAgICAgIE9yaWdpbmFsRXJyb3IuY2FwdHVyZVN0YWNrVHJhY2UoZXJyb3IsIFJlc3VsdEVycm9yKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gZXJyb3I7XG4gICAgICB9O1xuICAgICAgZGVmaW5lUHJvcGVydGllcyhSZXN1bHRFcnJvciwge1xuICAgICAgICBsZW5ndGg6IHsgdmFsdWU6IDEgfSxcbiAgICAgICAgcHJvdG90eXBlOiB7XG4gICAgICAgICAgdmFsdWU6IEVycm9yUHJvdG90eXBlLFxuICAgICAgICAgIHdyaXRhYmxlOiBmYWxzZSxcbiAgICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgICBjb25maWd1cmFibGU6IGZhbHNlLFxuICAgICAgICB9LFxuICAgICAgfSk7XG4gICAgICByZXR1cm4gUmVzdWx0RXJyb3I7XG4gICAgfTtcbiAgICBjb25zdCBJbml0aWFsRXJyb3IgPSBtYWtlRXJyb3JDb25zdHJ1Y3Rvcih7IHBvd2VyczogJ29yaWdpbmFsJyB9KTtcbiAgICBjb25zdCBTaGFyZWRFcnJvciA9IG1ha2VFcnJvckNvbnN0cnVjdG9yKHsgcG93ZXJzOiAnbm9uZScgfSk7XG4gICAgZGVmaW5lUHJvcGVydGllcyhFcnJvclByb3RvdHlwZSwge1xuICAgICAgY29uc3RydWN0b3I6IHsgdmFsdWU6IFNoYXJlZEVycm9yIH0sXG4gICAgICAvKiBUT0RPXG4gICAgICBzdGFjazoge1xuICAgICAgICBnZXQoKSB7XG4gICAgICAgICAgcmV0dXJuICcnO1xuICAgICAgICB9LFxuICAgICAgICBzZXQoXykge1xuICAgICAgICAgIC8vIGlnbm9yZVxuICAgICAgICB9LFxuICAgICAgfSxcbiAgICAgICovXG4gICAgfSk7XG5cbiAgICBmb3IgKGNvbnN0IE5hdGl2ZUVycm9yIG9mIE5hdGl2ZUVycm9ycykge1xuICAgICAgc2V0UHJvdG90eXBlT2YoTmF0aXZlRXJyb3IsIFNoYXJlZEVycm9yKTtcbiAgICB9XG5cbiAgICAvLyBodHRwczovL3Y4LmRldi9kb2NzL3N0YWNrLXRyYWNlLWFwaSNjb21wYXRpYmlsaXR5IGFkdmlzZXMgdGhhdFxuICAgIC8vIHByb2dyYW1tZXJzIGNhbiBcImFsd2F5c1wiIHNldCBgRXJyb3Iuc3RhY2tUcmFjZUxpbWl0YFxuICAgIC8vIGV2ZW4gb24gbm9uLXY4IHBsYXRmb3Jtcy4gT24gbm9uLXY4XG4gICAgLy8gaXQgd2lsbCBoYXZlIG5vIGVmZmVjdCwgYnV0IHRoaXMgYWR2aWNlIG9ubHkgbWFrZXMgc2Vuc2VcbiAgICAvLyBpZiB0aGUgYXNzaWdubWVudCBpdHNlbGYgZG9lcyBub3QgZmFpbCwgd2hpY2ggaXQgd291bGRcbiAgICAvLyBpZiBgRXJyb3JgIHdlcmUgbmFpdmVseSBmcm96ZW4uIEhlbmNlLCB3ZSBhZGQgc2V0dGVycyB0aGF0XG4gICAgLy8gYWNjZXB0IGJ1dCBpZ25vcmUgdGhlIGFzc2lnbm1lbnQgb24gbm9uLXY4IHBsYXRmb3Jtcy5cbiAgICBkZWZpbmVQcm9wZXJ0aWVzKEluaXRpYWxFcnJvciwge1xuICAgICAgc3RhY2tUcmFjZUxpbWl0OiB7XG4gICAgICAgIGdldCgpIHtcbiAgICAgICAgICBpZiAodHlwZW9mIE9yaWdpbmFsRXJyb3Iuc3RhY2tUcmFjZUxpbWl0ID09PSAnbnVtYmVyJykge1xuICAgICAgICAgICAgLy8gT3JpZ2luYWxFcnJvci5zdGFja1RyYWNlTGltaXQgaXMgb25seSBvbiB2OFxuICAgICAgICAgICAgcmV0dXJuIE9yaWdpbmFsRXJyb3Iuc3RhY2tUcmFjZUxpbWl0O1xuICAgICAgICAgIH1cbiAgICAgICAgICByZXR1cm4gdW5kZWZpbmVkO1xuICAgICAgICB9LFxuICAgICAgICBzZXQobmV3TGltaXQpIHtcbiAgICAgICAgICBpZiAodHlwZW9mIG5ld0xpbWl0ICE9PSAnbnVtYmVyJykge1xuICAgICAgICAgICAgLy8gc2lsZW50bHkgZG8gbm90aGluZy4gVGhpcyBiZWhhdmlvciBkb2Vzbid0IHByZWNpc2VseVxuICAgICAgICAgICAgLy8gZW11bGF0ZSB2OCBlZGdlLWNhc2UgYmVoYXZpb3IuIEJ1dCBnaXZlbiB0aGUgcHVycG9zZVxuICAgICAgICAgICAgLy8gb2YgdGhpcyBlbXVsYXRpb24sIGhhdmluZyBlZGdlIGNhc2VzIGVyciB0b3dhcmRzXG4gICAgICAgICAgICAvLyBoYXJtbGVzcyBzZWVtcyB0aGUgc2FmZXIgb3B0aW9uLlxuICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgIH1cbiAgICAgICAgICBpZiAodHlwZW9mIE9yaWdpbmFsRXJyb3Iuc3RhY2tUcmFjZUxpbWl0ID09PSAnbnVtYmVyJykge1xuICAgICAgICAgICAgLy8gT3JpZ2luYWxFcnJvci5zdGFja1RyYWNlTGltaXQgaXMgb25seSBvbiB2OFxuICAgICAgICAgICAgT3JpZ2luYWxFcnJvci5zdGFja1RyYWNlTGltaXQgPSBuZXdMaW1pdDtcbiAgICAgICAgICAgIC8vIFdlIHBsYWNlIHRoZSB1c2VsZXNzIHJldHVybiBvbiB0aGUgbmV4dCBsaW5lIHRvIGVuc3VyZVxuICAgICAgICAgICAgLy8gdGhhdCBhbnl0aGluZyB3ZSBwbGFjZSBhZnRlciB0aGUgaWYgaW4gdGhlIGZ1dHVyZSBvbmx5XG4gICAgICAgICAgICAvLyBoYXBwZW5zIGlmIHRoZSB0aGVuLWNhc2UgZG9lcyBub3QuXG4gICAgICAgICAgICAvLyBlc2xpbnQtZGlzYWJsZS1uZXh0LWxpbmUgbm8tdXNlbGVzcy1yZXR1cm5cbiAgICAgICAgICAgIHJldHVybjtcbiAgICAgICAgICB9XG4gICAgICAgIH0sXG4gICAgICAgIC8vIFdURiBvbiB2OCBzdGFja1RyYWNlTGltaXQgaXMgZW51bWVyYWJsZVxuICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlLFxuICAgICAgfSxcbiAgICB9KTtcblxuICAgIC8vIFRoZSBkZWZhdWx0IFNoYXJlZEVycm9yIG11Y2ggYmUgY29tcGxldGVseSBwb3dlcmxlc3MgZXZlbiBvbiB2OCxcbiAgICAvLyBzbyB0aGUgbGVuaWVudCBgc3RhY2tUcmFjZUxpbWl0YCBhY2Nlc3NvciBkb2VzIG5vdGhpbmcgb24gYWxsXG4gICAgLy8gcGxhdGZvcm1zLlxuICAgIGRlZmluZVByb3BlcnRpZXMoU2hhcmVkRXJyb3IsIHtcbiAgICAgIHN0YWNrVHJhY2VMaW1pdDoge1xuICAgICAgICBnZXQoKSB7XG4gICAgICAgICAgcmV0dXJuIHVuZGVmaW5lZDtcbiAgICAgICAgfSxcbiAgICAgICAgc2V0KF9uZXdMaW1pdCkge1xuICAgICAgICAgIC8vIGRvIG5vdGhpbmdcbiAgICAgICAgfSxcbiAgICAgICAgZW51bWVyYWJsZTogZmFsc2UsXG4gICAgICAgIGNvbmZpZ3VyYWJsZTogdHJ1ZSxcbiAgICAgIH0sXG4gICAgfSk7XG5cbiAgICBsZXQgaW5pdGlhbEdldFN0YWNrU3RyaW5nID0gdGFtZWRNZXRob2RzJDEuZ2V0U3RhY2tTdHJpbmc7XG4gICAgaWYgKHBsYXRmb3JtID09PSAndjgnKSB7XG4gICAgICBpbml0aWFsR2V0U3RhY2tTdHJpbmcgPSB0YW1lVjhFcnJvckNvbnN0cnVjdG9yKFxuICAgICAgICBPcmlnaW5hbEVycm9yLFxuICAgICAgICBJbml0aWFsRXJyb3IsXG4gICAgICAgIGVycm9yVGFtaW5nLFxuICAgICAgICBzdGFja0ZpbHRlcmluZyxcbiAgICAgICk7XG4gICAgfVxuICAgIHJldHVybiB7XG4gICAgICAnJUluaXRpYWxHZXRTdGFja1N0cmluZyUnOiBpbml0aWFsR2V0U3RhY2tTdHJpbmcsXG4gICAgICAnJUluaXRpYWxFcnJvciUnOiBJbml0aWFsRXJyb3IsXG4gICAgICAnJVNoYXJlZEVycm9yJSc6IFNoYXJlZEVycm9yLFxuICAgIH07XG4gIH1cblxuICAvLyBDb3B5cmlnaHQgKEMpIDIwMTggQWdvcmljXG5cbiAgLyoqXG4gICAqIEB0eXBlZGVmIHt7XG4gICAqICAgZGF0ZVRhbWluZz86ICdzYWZlJyB8ICd1bnNhZmUnLFxuICAgKiAgIGVycm9yVGFtaW5nPzogJ3NhZmUnIHwgJ3Vuc2FmZScsXG4gICAqICAgbWF0aFRhbWluZz86ICdzYWZlJyB8ICd1bnNhZmUnLFxuICAgKiAgIHJlZ0V4cFRhbWluZz86ICdzYWZlJyB8ICd1bnNhZmUnLFxuICAgKiAgIGxvY2FsZVRhbWluZz86ICdzYWZlJyB8ICd1bnNhZmUnLFxuICAgKiAgIGNvbnNvbGVUYW1pbmc/OiAnc2FmZScgfCAndW5zYWZlJyxcbiAgICogICBvdmVycmlkZVRhbWluZz86ICdtaW4nIHwgJ21vZGVyYXRlJyxcbiAgICogICBzdGFja0ZpbHRlcmluZz86ICdjb25jaXNlJyB8ICd2ZXJib3NlJyxcbiAgICogfX0gTG9ja2Rvd25PcHRpb25zXG4gICAqL1xuXG4gIGNvbnN0IHsgZGV0YWlsczogZCQzLCBxdW90ZTogcSQyIH0gPSBhc3NlcnQ7XG5cbiAgbGV0IGZpcnN0T3B0aW9ucztcblxuICAvLyBBIHN1Y2Nlc3NmdWwgbG9ja2Rvd24gY2FsbCBpbmRpY2F0ZXMgdGhhdCBgaGFyZGVuYCBjYW4gYmUgY2FsbGVkIGFuZFxuICAvLyBndWFyYW50ZWUgdGhhdCB0aGUgaGFyZGVuZWQgb2JqZWN0IGdyYXBoIGlzIGZyb3plbiBvdXQgdG8gdGhlIGZyaW5nZS5cbiAgbGV0IGxvY2tlZERvd24gPSBmYWxzZTtcblxuICAvLyBCdWlsZCBhIGhhcmRlbigpIHdpdGggYW4gZW1wdHkgZnJpbmdlLlxuICAvLyBHYXRlIGl0IG9uIGxvY2tkb3duLlxuICBjb25zdCBsb2NrZG93bkhhcmRlbiA9IG1ha2VIYXJkZW5lcigpO1xuXG4gIC8qKlxuICAgKiBAdGVtcGxhdGUgVFxuICAgKiBAcGFyYW0ge1R9IHJlZlxuICAgKiBAcmV0dXJucyB7VH1cbiAgICovXG4gIGNvbnN0IGhhcmRlbiA9IHJlZiA9PiB7XG4gICAgYXNzZXJ0KGxvY2tlZERvd24sICdDYW5ub3QgaGFyZGVuIGJlZm9yZSBsb2NrZG93bicpO1xuICAgIHJldHVybiBsb2NrZG93bkhhcmRlbihyZWYpO1xuICB9O1xuXG4gIGNvbnN0IGFscmVhZHlIYXJkZW5lZEludHJpbnNpY3MgPSAoKSA9PiBmYWxzZTtcblxuICAvKipcbiAgICogQGNhbGxiYWNrIFRyYW5zZm9ybVxuICAgKiBAcGFyYW0ge3N0cmluZ30gc291cmNlXG4gICAqIEByZXR1cm5zIHtzdHJpbmd9XG4gICAqL1xuXG4gIC8qKlxuICAgKiBAY2FsbGJhY2sgQ29tcGFydG1lbnRDb25zdHJ1Y3RvclxuICAgKiBAcGFyYW0ge09iamVjdH0gZW5kb3dtZW50c1xuICAgKiBAcGFyYW0ge09iamVjdH0gbW9kdWxlTWFwXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBbb3B0aW9uc11cbiAgICogQHBhcmFtIHtBcnJheTxUcmFuc2Zvcm0+fSBbb3B0aW9ucy50cmFuc2Zvcm1zXVxuICAgKiBAcGFyYW0ge0FycmF5PFRyYW5zZm9ybT59IFtvcHRpb25zLl9fc2hpbVRyYW5zZm9ybXNfX11cbiAgICogQHBhcmFtIHtPYmplY3R9IFtvcHRpb25zLmdsb2JhbExleGljYWxzXVxuICAgKi9cblxuICAvKipcbiAgICogQGNhbGxiYWNrIENvbXBhcnRtZW50Q29uc3RydWN0b3JNYWtlclxuICAgKiBAcGFyYW0ge0NvbXBhcnRtZW50Q29uc3RydWN0b3JNYWtlcn0gdGFyZ2V0TWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3JcbiAgICogQHBhcmFtIHtPYmplY3R9IGludHJpbnNpY3NcbiAgICogQHBhcmFtIHsoZnVuYzogRnVuY3Rpb24pID0+IHZvaWR9IG5hdGl2ZUJyYW5kZXJcbiAgICogQHJldHVybnMge0NvbXBhcnRtZW50Q29uc3RydWN0b3J9XG4gICAqL1xuXG4gIC8qKlxuICAgKiBAcGFyYW0ge0NvbXBhcnRtZW50Q29uc3RydWN0b3JNYWtlcn0gbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3JcbiAgICogQHBhcmFtIHtPYmplY3R9IGNvbXBhcnRtZW50UHJvdG90eXBlXG4gICAqIEBwYXJhbSB7KCkgPT4gT2JqZWN0fSBnZXRBbm9ueW1vdXNJbnRyaW5zaWNzXG4gICAqIEBwYXJhbSB7TG9ja2Rvd25PcHRpb25zfSBbb3B0aW9uc11cbiAgICogQHJldHVybnMgeygpID0+IHt9fSByZXBhaXJJbnRyaW5zaWNzXG4gICAqL1xuICBmdW5jdGlvbiByZXBhaXJJbnRyaW5zaWNzKFxuICAgIG1ha2VDb21wYXJ0bWVudENvbnN0cnVjdG9yLFxuICAgIGNvbXBhcnRtZW50UHJvdG90eXBlLFxuICAgIGdldEFub255bW91c0ludHJpbnNpY3MsXG4gICAgb3B0aW9ucyA9IHt9LFxuICApIHtcbiAgICAvLyBGaXJzdCB0aW1lLCBhYnNlbnQgb3B0aW9ucyBkZWZhdWx0IHRvICdzYWZlJy5cbiAgICAvLyBTdWJzZXF1ZW50IHRpbWVzLCBhYnNlbnQgb3B0aW9ucyBkZWZhdWx0IHRvIGZpcnN0IG9wdGlvbnMuXG4gICAgLy8gVGh1cywgYWxsIHByZXNlbnQgb3B0aW9ucyBtdXN0IGFncmVlIHdpdGggZmlyc3Qgb3B0aW9ucy5cbiAgICAvLyBSZWNvbnN0cnVjdGluZyBgb3B0aW9uYCBoZXJlIGFsc28gZW5zdXJlcyB0aGF0IGl0IGlzIGEgd2VsbFxuICAgIC8vIGJlaGF2ZWQgcmVjb3JkLCB3aXRoIG9ubHkgb3duIGRhdGEgcHJvcGVydGllcy5cbiAgICAvL1xuICAgIC8vIFRoZSBgb3ZlcnJpZGVUYW1pbmdgIGlzIG5vdCBhIHNhZmV0eSBpc3N1ZS4gUmF0aGVyIGl0IGlzIGEgdHJhZGVvZmZcbiAgICAvLyBiZXR3ZWVuIGNvZGUgY29tcGF0aWJpbGl0eSwgd2hpY2ggaXMgYmV0dGVyIHdpdGggdGhlIGAnbW9kZXJhdGUnYFxuICAgIC8vIHNldHRpbmcsIGFuZCB0b29sIGNvbXBhdGliaWxpdHksIHdoaWNoIGlzIGJldHRlciB3aXRoIHRoZSBgJ21pbidgXG4gICAgLy8gc2V0dGluZy4gU2VlXG4gICAgLy8gaHR0cHM6Ly9naXRodWIuY29tL0Fnb3JpYy9TRVMtc2hpbS9ibG9iL21hc3Rlci9wYWNrYWdlcy9zZXMvUkVBRE1FLm1kI2VuYWJsaW5nLW92ZXJyaWRlLWJ5LWFzc2lnbm1lbnQpXG4gICAgLy8gZm9yIGFuIGV4cGxhbmF0aW9uIG9mIHdoZW4gdG8gdXNlIHdoaWNoLlxuICAgIC8vXG4gICAgLy8gVGhlIGBzdGFja0ZpbHRlcmluZ2AgaXMgbm90IGEgc2FmZXR5IGlzc3VlLiBSYXRoZXIgaXQgaXMgYSB0cmFkZW9mZlxuICAgIC8vIGJldHdlZW4gcmVsZXZhbmNlIGFuZCBjb21wbGV0ZW5lc3Mgb2YgdGhlIHN0YWNrIGZyYW1lcyBzaG93biBvbiB0aGVcbiAgICAvLyBjb25zb2xlLiBTZXR0aW5nYHN0YWNrRmlsdGVyaW5nYCB0byBgJ3ZlcmJvc2UnYCBhcHBsaWVzIG5vIGZpbHRlcnMsIHByb3ZpZGluZ1xuICAgIC8vIHRoZSByYXcgc3RhY2sgZnJhbWVzIHRoYXQgY2FuIGJlIHF1aXRlIHZlcnNib3NlLiBTZXR0aW5nXG4gICAgLy8gYHN0YWNrRnJhbWVGaWx0ZXJpbmdgIHRvYCdjb25jaXNlJ2AgbGltaXRzIHRoZSBkaXNwbGF5IHRvIHRoZSBzdGFjayBmcmFtZVxuICAgIC8vIGluZm9ybWF0aW9uIG1vc3QgbGlrZWx5IHRvIGJlIHJlbGV2YW50LCBlbGltaW5hdGluZyBkaXN0cmFjdGluZyBmcmFtZXNcbiAgICAvLyBzdWNoIGFzIHRob3NlIGZyb20gdGhlIGluZnJhc3RydWN0dXJlLiBIb3dldmVyLCB0aGUgYnVnIHlvdSdyZSB0cnlpbmcgdG9cbiAgICAvLyB0cmFjayBkb3duIG1pZ2h0IGJlIGluIHRoZSBpbmZyYXN0cnVyZSwgaW4gd2hpY2ggY2FzZSB0aGUgYCd2ZXJib3NlJ2Agc2V0dGluZ1xuICAgIC8vIGlzIHVzZWZ1bC4gU2VlXG4gICAgLy8gW2BzdGFja0ZpbHRlcmluZ2Agb3B0aW9uc10oaHR0cHM6Ly9naXRodWIuY29tL0Fnb3JpYy9TRVMtc2hpbS9ibG9iL21hc3Rlci9wYWNrYWdlcy9zZXMvbG9ja2Rvd24tb3B0aW9ucy5tZCNzdGFja2ZpbHRlcmluZy1vcHRpb25zKVxuICAgIC8vIGZvciBhbiBleHBsYW5hdGlvbi5cbiAgICBvcHRpb25zID0gLyoqIEB0eXBlIHtMb2NrZG93bk9wdGlvbnN9ICovICh7IC4uLmZpcnN0T3B0aW9ucywgLi4ub3B0aW9ucyB9KTtcbiAgICBjb25zdCB7XG4gICAgICBkYXRlVGFtaW5nID0gJ3NhZmUnLFxuICAgICAgZXJyb3JUYW1pbmcgPSAnc2FmZScsXG4gICAgICBtYXRoVGFtaW5nID0gJ3NhZmUnLFxuICAgICAgcmVnRXhwVGFtaW5nID0gJ3NhZmUnLFxuICAgICAgbG9jYWxlVGFtaW5nID0gJ3NhZmUnLFxuICAgICAgY29uc29sZVRhbWluZyA9ICdzYWZlJyxcbiAgICAgIG92ZXJyaWRlVGFtaW5nID0gJ21vZGVyYXRlJyxcbiAgICAgIHN0YWNrRmlsdGVyaW5nID0gJ2NvbmNpc2UnLFxuXG4gICAgICAuLi5leHRyYU9wdGlvbnNcbiAgICB9ID0gb3B0aW9ucztcblxuICAgIC8vIEFzc2VydCB0aGF0IG9ubHkgc3VwcG9ydGVkIG9wdGlvbnMgd2VyZSBwYXNzZWQuXG4gICAgLy8gVXNlIFJlZmxlY3Qub3duS2V5cyB0byByZWplY3Qgc3ltYm9sLW5hbWVkIHByb3BlcnRpZXMgYXMgd2VsbC5cbiAgICBjb25zdCBleHRyYU9wdGlvbnNOYW1lcyA9IFJlZmxlY3Qub3duS2V5cyhleHRyYU9wdGlvbnMpO1xuICAgIGFzc2VydChcbiAgICAgIGV4dHJhT3B0aW9uc05hbWVzLmxlbmd0aCA9PT0gMCxcbiAgICAgIGQkM2Bsb2NrZG93bigpOiBub24gc3VwcG9ydGVkIG9wdGlvbiAke3EkMihleHRyYU9wdGlvbnNOYW1lcyl9YCxcbiAgICApO1xuXG4gICAgLy8gQXNzZXJ0cyBmb3IgbXVsdGlwbGUgaW52b2NhdGlvbiBvZiBsb2NrZG93bigpLlxuICAgIGlmIChmaXJzdE9wdGlvbnMpIHtcbiAgICAgIGZvciAoY29uc3QgbmFtZSBvZiBrZXlzKGZpcnN0T3B0aW9ucykpIHtcbiAgICAgICAgYXNzZXJ0KFxuICAgICAgICAgIG9wdGlvbnNbbmFtZV0gPT09IGZpcnN0T3B0aW9uc1tuYW1lXSxcbiAgICAgICAgICBkJDNgbG9ja2Rvd24oKTogY2Fubm90IHJlLWludm9rZSB3aXRoIGRpZmZlcmVudCBvcHRpb24gJHtxJDIobmFtZSl9YCxcbiAgICAgICAgKTtcbiAgICAgIH1cbiAgICAgIHJldHVybiBhbHJlYWR5SGFyZGVuZWRJbnRyaW5zaWNzO1xuICAgIH1cblxuICAgIGZpcnN0T3B0aW9ucyA9IHtcbiAgICAgIGRhdGVUYW1pbmcsXG4gICAgICBlcnJvclRhbWluZyxcbiAgICAgIG1hdGhUYW1pbmcsXG4gICAgICByZWdFeHBUYW1pbmcsXG4gICAgICBsb2NhbGVUYW1pbmcsXG4gICAgICBjb25zb2xlVGFtaW5nLFxuICAgICAgb3ZlcnJpZGVUYW1pbmcsXG4gICAgICBzdGFja0ZpbHRlcmluZyxcbiAgICB9O1xuXG4gICAgLyoqXG4gICAgICogMS4gVEFNRSBwb3dlcnMgJiBnYXRoZXIgaW50cmluc2ljcyBmaXJzdC5cbiAgICAgKi9cbiAgICBjb25zdCBpbnRyaW5zaWNzQ29sbGVjdG9yID0gbWFrZUludHJpbnNpY3NDb2xsZWN0b3IoKTtcblxuICAgIGludHJpbnNpY3NDb2xsZWN0b3IuYWRkSW50cmluc2ljcyh0YW1lRnVuY3Rpb25Db25zdHJ1Y3RvcnMoKSk7XG5cbiAgICBpbnRyaW5zaWNzQ29sbGVjdG9yLmFkZEludHJpbnNpY3ModGFtZURhdGVDb25zdHJ1Y3RvcihkYXRlVGFtaW5nKSk7XG4gICAgaW50cmluc2ljc0NvbGxlY3Rvci5hZGRJbnRyaW5zaWNzKFxuICAgICAgdGFtZUVycm9yQ29uc3RydWN0b3IoZXJyb3JUYW1pbmcsIHN0YWNrRmlsdGVyaW5nKSxcbiAgICApO1xuICAgIGludHJpbnNpY3NDb2xsZWN0b3IuYWRkSW50cmluc2ljcyh0YW1lTWF0aE9iamVjdChtYXRoVGFtaW5nKSk7XG4gICAgaW50cmluc2ljc0NvbGxlY3Rvci5hZGRJbnRyaW5zaWNzKHRhbWVSZWdFeHBDb25zdHJ1Y3RvcihyZWdFeHBUYW1pbmcpKTtcblxuICAgIGludHJpbnNpY3NDb2xsZWN0b3IuYWRkSW50cmluc2ljcyhnZXRBbm9ueW1vdXNJbnRyaW5zaWNzKCkpO1xuXG4gICAgaW50cmluc2ljc0NvbGxlY3Rvci5jb21wbGV0ZVByb3RvdHlwZXMoKTtcblxuICAgIGNvbnN0IGludHJpbnNpY3MgPSBpbnRyaW5zaWNzQ29sbGVjdG9yLmZpbmFsSW50cmluc2ljcygpO1xuXG4gICAgLy8gV3JhcCBjb25zb2xlIHVubGVzcyBzdXBwcmVzc2VkLlxuICAgIC8vIEF0IHRoZSBtb21lbnQsIHRoZSBjb25zb2xlIGlzIGNvbnNpZGVyZWQgYSBob3N0IHBvd2VyIGluIHRoZSBzdGFydFxuICAgIC8vIGNvbXBhcnRtZW50LCBhbmQgbm90IGEgcHJpbW9yZGlhbC4gSGVuY2UgaXQgaXMgYWJzZW50IGZyb20gdGhlIHdoaWxlbGlzdFxuICAgIC8vIGFuZCBieXBhc3NlcyB0aGUgaW50cmluc2ljc0NvbGxlY3Rvci5cbiAgICBsZXQgb3B0R2V0U3RhY2tTdHJpbmc7XG4gICAgaWYgKGVycm9yVGFtaW5nICE9PSAndW5zYWZlJykge1xuICAgICAgb3B0R2V0U3RhY2tTdHJpbmcgPSBpbnRyaW5zaWNzWyclSW5pdGlhbEdldFN0YWNrU3RyaW5nJSddO1xuICAgIH1cbiAgICBjb25zdCBjb25zb2xlUmVjb3JkID0gdGFtZUNvbnNvbGUoY29uc29sZVRhbWluZywgb3B0R2V0U3RhY2tTdHJpbmcpO1xuICAgIGdsb2JhbFRoaXMuY29uc29sZSA9IC8qKiBAdHlwZSB7Q29uc29sZX0gKi8gKGNvbnNvbGVSZWNvcmQuY29uc29sZSk7XG5cbiAgICAvLyBSZXBsYWNlICpMb2NhbGUqIG1ldGhvZHMgd2l0aCB0aGVpciBub24tbG9jYWxlIGVxdWl2YWxlbnRzXG4gICAgdGFtZUxvY2FsZU1ldGhvZHMoaW50cmluc2ljcywgbG9jYWxlVGFtaW5nKTtcblxuICAgIC8vIFJlcGxhY2UgRnVuY3Rpb24ucHJvdG90eXBlLnRvU3RyaW5nIHdpdGggb25lIHRoYXQgcmVjb2duaXplc1xuICAgIC8vIHNoaW1tZWQgZnVuY3Rpb25zIGFzIGhvbm9yYXJ5IG5hdGl2ZSBmdW5jdGlvbnMuXG4gICAgY29uc3QgbmF0aXZlQnJhbmRlciA9IHRhbWVGdW5jdGlvblRvU3RyaW5nKCk7XG5cbiAgICAvKipcbiAgICAgKiAyLiBXSElURUxJU1QgdG8gc3RhbmRhcmRpemUgdGhlIGVudmlyb25tZW50LlxuICAgICAqL1xuXG4gICAgLy8gUmVtb3ZlIG5vbi1zdGFuZGFyZCBwcm9wZXJ0aWVzLlxuICAgIC8vIEFsbCByZW1haW5pbmcgZnVuY3Rpb24gZW5jb3VudGVyZWQgZHVyaW5nIHdoaXRlbGlzdGluZyBhcmVcbiAgICAvLyBicmFuZGVkIGFzIGhvbm9yYXJ5IG5hdGl2ZSBmdW5jdGlvbnMuXG4gICAgd2hpdGVsaXN0SW50cmluc2ljcyhpbnRyaW5zaWNzLCBuYXRpdmVCcmFuZGVyKTtcblxuICAgIC8vIFJlcGFpciBwcm9ibGVtcyB3aXRoIGxlZ2FjeSBhY2Nlc3NvcnMgaWYgbmVjZXNzYXJ5LlxuICAgIHJlcGFpckxlZ2FjeUFjY2Vzc29ycygpO1xuXG4gICAgLy8gSW5pdGlhbGl6ZSB0aGUgcG93ZXJmdWwgaW5pdGlhbCBnbG9iYWwsIGkuZS4sIHRoZSBnbG9iYWwgb2YgdGhlXG4gICAgLy8gc3RhcnQgY29tcGFydG1lbnQsIGZyb20gdGhlIGludHJpbnNpY3MuXG4gICAgaW5pdEdsb2JhbE9iamVjdChcbiAgICAgIGdsb2JhbFRoaXMsXG4gICAgICBpbnRyaW5zaWNzLFxuICAgICAgaW5pdGlhbEdsb2JhbFByb3BlcnR5TmFtZXMsXG4gICAgICBtYWtlQ29tcGFydG1lbnRDb25zdHJ1Y3RvcixcbiAgICAgIGNvbXBhcnRtZW50UHJvdG90eXBlLFxuICAgICAge1xuICAgICAgICBuYXRpdmVCcmFuZGVyLFxuICAgICAgfSxcbiAgICApO1xuXG4gICAgLyoqXG4gICAgICogMy4gSEFSREVOIHRvIHNoYXJlIHRoZSBpbnRyaW5zaWNzLlxuICAgICAqL1xuXG4gICAgZnVuY3Rpb24gaGFyZGVuSW50cmluc2ljcygpIHtcbiAgICAgIC8vIENpcmN1bXZlbnQgdGhlIG92ZXJyaWRlIG1pc3Rha2UuXG4gICAgICBlbmFibGVQcm9wZXJ0eU92ZXJyaWRlcyhpbnRyaW5zaWNzLCBvdmVycmlkZVRhbWluZyk7XG5cbiAgICAgIC8vIEZpbmFsbHkgcmVnaXN0ZXIgYW5kIG9wdGlvbmFsbHkgZnJlZXplIGFsbCB0aGUgaW50cmluc2ljcy4gVGhpc1xuICAgICAgLy8gbXVzdCBiZSB0aGUgb3BlcmF0aW9uIHRoYXQgbW9kaWZpZXMgdGhlIGludHJpbnNpY3MuXG4gICAgICBsb2NrZG93bkhhcmRlbihpbnRyaW5zaWNzKTtcblxuICAgICAgLy8gSGF2aW5nIGNvbXBsZXRlZCBsb2NrZG93biB3aXRob3V0IGZhaWxpbmcsIHRoZSB1c2VyIG1heSBub3dcbiAgICAgIC8vIGNhbGwgYGhhcmRlbmAgYW5kIGV4cGVjdCB0aGUgb2JqZWN0J3MgdHJhbnNpdGl2ZWx5IGFjY2Vzc2libGUgcHJvcGVydGllc1xuICAgICAgLy8gdG8gYmUgZnJvemVuIG91dCB0byB0aGUgZnJpbmdlLlxuICAgICAgLy8gUmFpc2UgdGhlIGBoYXJkZW5gIGdhdGUuXG4gICAgICBsb2NrZWREb3duID0gdHJ1ZTtcblxuICAgICAgLy8gUmV0dXJuaW5nIGB0cnVlYCBpbmRpY2F0ZXMgdGhhdCB0aGlzIGlzIGEgSlMgdG8gU0VTIHRyYW5zaXRpb24uXG4gICAgICByZXR1cm4gdHJ1ZTtcbiAgICB9XG5cbiAgICByZXR1cm4gaGFyZGVuSW50cmluc2ljcztcbiAgfVxuXG4gIC8qKlxuICAgKiBAcGFyYW0ge0NvbXBhcnRtZW50Q29uc3RydWN0b3JNYWtlcn0gbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3JcbiAgICogQHBhcmFtIHtPYmplY3R9IGNvbXBhcnRtZW50UHJvdG90eXBlXG4gICAqIEBwYXJhbSB7KCkgPT4gT2JqZWN0fSBnZXRBbm9ueW1vdXNJbnRyaW5zaWNzXG4gICAqL1xuICBjb25zdCBtYWtlTG9ja2Rvd24gPSAoXG4gICAgbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3IsXG4gICAgY29tcGFydG1lbnRQcm90b3R5cGUsXG4gICAgZ2V0QW5vbnltb3VzSW50cmluc2ljcyxcbiAgKSA9PiB7XG4gICAgLyoqXG4gICAgICogQHBhcmFtIHtMb2NrZG93bk9wdGlvbnN9IFtvcHRpb25zXVxuICAgICAqL1xuICAgIGNvbnN0IGxvY2tkb3duID0gKG9wdGlvbnMgPSB7fSkgPT4ge1xuICAgICAgY29uc3QgbWF5YmVIYXJkZW5JbnRyaW5zaWNzID0gcmVwYWlySW50cmluc2ljcyhcbiAgICAgICAgbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3IsXG4gICAgICAgIGNvbXBhcnRtZW50UHJvdG90eXBlLFxuICAgICAgICBnZXRBbm9ueW1vdXNJbnRyaW5zaWNzLFxuICAgICAgICBvcHRpb25zLFxuICAgICAgKTtcbiAgICAgIHJldHVybiBtYXliZUhhcmRlbkludHJpbnNpY3MoKTtcbiAgICB9O1xuICAgIHJldHVybiBsb2NrZG93bjtcbiAgfTtcblxuICAvKiogQHR5cGVkZWYge1JldHVyblR5cGU8dHlwZW9mIG1ha2VMb2NrZG93bj59IExvY2tkb3duICovXG5cbiAgLy8gQHRzLWNoZWNrXG5cbiAgLy8gcHJpdmF0ZUZpZWxkcyBjYXB0dXJlcyB0aGUgcHJpdmF0ZSBzdGF0ZSBmb3IgZWFjaCBjb21wYXJ0bWVudC5cbiAgY29uc3QgcHJpdmF0ZUZpZWxkcyA9IG5ldyBXZWFrTWFwKCk7XG5cbiAgLyoqXG4gICAqIEB0eXBlZGVmIHsoc291cmNlOiBzdHJpbmcpID0+IHN0cmluZ30gVHJhbnNmb3JtXG4gICAqL1xuXG4gIGNvbnN0IENvbXBhcnRtZW50UHJvdG90eXBlID0ge1xuICAgIGNvbnN0cnVjdG9yOiBJbmVydENvbXBhcnRtZW50LFxuXG4gICAgZ2V0IGdsb2JhbFRoaXMoKSB7XG4gICAgICByZXR1cm4gcHJpdmF0ZUZpZWxkcy5nZXQodGhpcykuZ2xvYmFsT2JqZWN0O1xuICAgIH0sXG5cbiAgICBnZXQgbmFtZSgpIHtcbiAgICAgIHJldHVybiBwcml2YXRlRmllbGRzLmdldCh0aGlzKS5uYW1lO1xuICAgIH0sXG5cbiAgICAvKipcbiAgICAgKiBAcGFyYW0ge3N0cmluZ30gc291cmNlIGlzIGEgSmF2YVNjcmlwdCBwcm9ncmFtIGdyYW1tYXIgY29uc3RydWN0aW9uLlxuICAgICAqIEBwYXJhbSB7T2JqZWN0fSBbb3B0aW9uc11cbiAgICAgKiBAcGFyYW0ge0FycmF5PFRyYW5zZm9ybT59IFtvcHRpb25zLnRyYW5zZm9ybXNdXG4gICAgICogQHBhcmFtIHtib29sZWFufSBbb3B0aW9ucy5zbG9wcHlHbG9iYWxzTW9kZV1cbiAgICAgKiBAcGFyYW0ge09iamVjdH0gW29wdGlvbnMuX19tb2R1bGVTaGltTGV4aWNhbHNfX11cbiAgICAgKiBAcGFyYW0ge2Jvb2xlYW59IFtvcHRpb25zLl9fZXZhZGVIdG1sQ29tbWVudFRlc3RfX11cbiAgICAgKiBAcGFyYW0ge2Jvb2xlYW59IFtvcHRpb25zLl9fZXZhZGVJbXBvcnRFeHByZXNzaW9uVGVzdF9fXVxuICAgICAqIEBwYXJhbSB7Ym9vbGVhbn0gW29wdGlvbnMuX19yZWplY3RTb21lRGlyZWN0RXZhbEV4cHJlc3Npb25zX19dXG4gICAgICovXG4gICAgZXZhbHVhdGUoc291cmNlLCBvcHRpb25zID0ge30pIHtcbiAgICAgIC8vIFBlcmZvcm0gdGhpcyBjaGVjayBmaXJzdCB0byBhdm9pZCB1bmVjZXNzYXJ5IHNhbml0aXppbmcuXG4gICAgICAvLyBUT0RPIE1heWJlIHJlbGF4IHN0cmluZyBjaGVjayBhbmQgY29lcmNlIGluc3RlYWQ6XG4gICAgICAvLyBodHRwczovL2dpdGh1Yi5jb20vdGMzOS9wcm9wb3NhbC1keW5hbWljLWNvZGUtYnJhbmQtY2hlY2tzXG4gICAgICBpZiAodHlwZW9mIHNvdXJjZSAhPT0gJ3N0cmluZycpIHtcbiAgICAgICAgdGhyb3cgbmV3IFR5cGVFcnJvcignZmlyc3QgYXJndW1lbnQgb2YgZXZhbHVhdGUoKSBtdXN0IGJlIGEgc3RyaW5nJyk7XG4gICAgICB9XG5cbiAgICAgIC8vIEV4dHJhY3Qgb3B0aW9ucywgYW5kIHNoYWxsb3ctY2xvbmUgdHJhbnNmb3Jtcy5cbiAgICAgIGNvbnN0IHtcbiAgICAgICAgdHJhbnNmb3JtcyA9IFtdLFxuICAgICAgICBzbG9wcHlHbG9iYWxzTW9kZSA9IGZhbHNlLFxuICAgICAgICBfX21vZHVsZVNoaW1MZXhpY2Fsc19fID0gdW5kZWZpbmVkLFxuICAgICAgICBfX2V2YWRlSHRtbENvbW1lbnRUZXN0X18gPSBmYWxzZSxcbiAgICAgICAgX19ldmFkZUltcG9ydEV4cHJlc3Npb25UZXN0X18gPSBmYWxzZSxcbiAgICAgICAgX19yZWplY3RTb21lRGlyZWN0RXZhbEV4cHJlc3Npb25zX18gPSB0cnVlLCAvLyBOb3RlIGRlZmF1bHQgb25cbiAgICAgIH0gPSBvcHRpb25zO1xuICAgICAgY29uc3QgbG9jYWxUcmFuc2Zvcm1zID0gWy4uLnRyYW5zZm9ybXNdO1xuICAgICAgaWYgKF9fZXZhZGVIdG1sQ29tbWVudFRlc3RfXyA9PT0gdHJ1ZSkge1xuICAgICAgICBsb2NhbFRyYW5zZm9ybXMucHVzaChldmFkZUh0bWxDb21tZW50VGVzdCk7XG4gICAgICB9XG4gICAgICBpZiAoX19ldmFkZUltcG9ydEV4cHJlc3Npb25UZXN0X18gPT09IHRydWUpIHtcbiAgICAgICAgbG9jYWxUcmFuc2Zvcm1zLnB1c2goZXZhZGVJbXBvcnRFeHByZXNzaW9uVGVzdCk7XG4gICAgICB9XG4gICAgICBpZiAoX19yZWplY3RTb21lRGlyZWN0RXZhbEV4cHJlc3Npb25zX18gPT09IHRydWUpIHtcbiAgICAgICAgbG9jYWxUcmFuc2Zvcm1zLnB1c2gocmVqZWN0U29tZURpcmVjdEV2YWxFeHByZXNzaW9ucyk7XG4gICAgICB9XG5cbiAgICAgIGNvbnN0IGNvbXBhcnRtZW50RmllbGRzID0gcHJpdmF0ZUZpZWxkcy5nZXQodGhpcyk7XG4gICAgICBsZXQgeyBnbG9iYWxUcmFuc2Zvcm1zIH0gPSBjb21wYXJ0bWVudEZpZWxkcztcbiAgICAgIGNvbnN0IHtcbiAgICAgICAgZ2xvYmFsT2JqZWN0LFxuICAgICAgICBnbG9iYWxMZXhpY2FscyxcbiAgICAgICAga25vd25TY29wZVByb3hpZXMsXG4gICAgICB9ID0gY29tcGFydG1lbnRGaWVsZHM7XG5cbiAgICAgIGxldCBsb2NhbE9iamVjdCA9IGdsb2JhbExleGljYWxzO1xuICAgICAgaWYgKF9fbW9kdWxlU2hpbUxleGljYWxzX18gIT09IHVuZGVmaW5lZCkge1xuICAgICAgICAvLyBXaGVuIHVzaW5nIGBldmFsdWF0ZWAgZm9yIEVTTSBtb2R1bGVzLCBhcyBzaG91bGQgb25seSBvY2N1ciBmcm9tIHRoZVxuICAgICAgICAvLyBtb2R1bGUtc2hpbSdzIG1vZHVsZS1pbnN0YW5jZS5qcywgd2UgZG8gbm90IHJldmVhbCB0aGUgU0VTLXNoaW0nc1xuICAgICAgICAvLyBtb2R1bGUtdG8tcHJvZ3JhbSB0cmFuc2xhdGlvbiwgYXMgdGhpcyBpcyBub3Qgc3RhbmRhcmRpemFibGUgYmVoYXZpb3IuXG4gICAgICAgIC8vIEhvd2V2ZXIsIHRoZSBgbG9jYWxUcmFuc2Zvcm1zYCB3aWxsIGNvbWUgZnJvbSB0aGUgYF9fc2hpbVRyYW5zZm9ybXNfX2BcbiAgICAgICAgLy8gQ29tcGFydG1lbnQgb3B0aW9uIGluIHRoaXMgY2FzZSwgd2hpY2ggaXMgYSBub24tc3RhbmRhcmRpemFibGUgZXNjYXBlXG4gICAgICAgIC8vIGhhdGNoIHNvIHByb2dyYW1zIGRlc2lnbmVkIHNwZWNpZmljYWxseSBmb3IgdGhlIFNFUy1zaGltXG4gICAgICAgIC8vIGltcGxlbWVudGF0aW9uIG1heSBvcHQtaW4gdG8gdXNlIHRoZSBzYW1lIHRyYW5zZm9ybXMgZm9yIGBldmFsdWF0ZWBcbiAgICAgICAgLy8gYW5kIGBpbXBvcnRgLCBhdCB0aGUgZXhwZW5zZSBvZiBiZWluZyB0aWdodGx5IGNvdXBsZWQgdG8gU0VTLXNoaW0uXG4gICAgICAgIGdsb2JhbFRyYW5zZm9ybXMgPSB1bmRlZmluZWQ7XG5cbiAgICAgICAgbG9jYWxPYmplY3QgPSBjcmVhdGUobnVsbCwgZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9ycyhnbG9iYWxMZXhpY2FscykpO1xuICAgICAgICBkZWZpbmVQcm9wZXJ0aWVzKFxuICAgICAgICAgIGxvY2FsT2JqZWN0LFxuICAgICAgICAgIGdldE93blByb3BlcnR5RGVzY3JpcHRvcnMoX19tb2R1bGVTaGltTGV4aWNhbHNfXyksXG4gICAgICAgICk7XG4gICAgICB9XG5cbiAgICAgIHJldHVybiBwZXJmb3JtRXZhbChzb3VyY2UsIGdsb2JhbE9iamVjdCwgbG9jYWxPYmplY3QsIHtcbiAgICAgICAgZ2xvYmFsVHJhbnNmb3JtcyxcbiAgICAgICAgbG9jYWxUcmFuc2Zvcm1zLFxuICAgICAgICBzbG9wcHlHbG9iYWxzTW9kZSxcbiAgICAgICAga25vd25TY29wZVByb3hpZXMsXG4gICAgICB9KTtcbiAgICB9LFxuXG4gICAgdG9TdHJpbmcoKSB7XG4gICAgICByZXR1cm4gJ1tvYmplY3QgQ29tcGFydG1lbnRdJztcbiAgICB9LFxuXG4gICAgLyogZXNsaW50LWRpc2FibGUtbmV4dC1saW5lIG5vLXVuZGVyc2NvcmUtZGFuZ2xlICovXG4gICAgX19pc0tub3duU2NvcGVQcm94eV9fKHZhbHVlKSB7XG4gICAgICByZXR1cm4gcHJpdmF0ZUZpZWxkcy5nZXQodGhpcykua25vd25TY29wZVByb3hpZXMuaGFzKHZhbHVlKTtcbiAgICB9LFxuICB9O1xuXG4gIGRlZmluZVByb3BlcnRpZXMoSW5lcnRDb21wYXJ0bWVudCwge1xuICAgIHByb3RvdHlwZTogeyB2YWx1ZTogQ29tcGFydG1lbnRQcm90b3R5cGUgfSxcbiAgfSk7XG5cbiAgLyoqXG4gICAqIEBjYWxsYmFjayBDb21wYXJ0bWVudENvbnN0cnVjdG9yXG4gICAqIEVhY2ggQ29tcGFydG1lbnQgY29uc3RydWN0b3IgaXMgYSBnbG9iYWwuIEEgaG9zdCB0aGF0IHdhbnRzIHRvIGV4ZWN1dGVcbiAgICogY29kZSBpbiBhIGNvbnRleHQgYm91bmQgdG8gYSBuZXcgZ2xvYmFsIGNyZWF0ZXMgYSBuZXcgY29tcGFydG1lbnQuXG4gICAqXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBlbmRvd21lbnRzXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBfbW9kdWxlTWFwXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBbb3B0aW9uc11cbiAgICogQHBhcmFtIHtzdHJpbmd9IFtvcHRpb25zLm5hbWVdXG4gICAqIEBwYXJhbSB7QXJyYXk8VHJhbnNmb3JtPn0gW29wdGlvbnMudHJhbnNmb3Jtc11cbiAgICogQHBhcmFtIHtBcnJheTxUcmFuc2Zvcm0+fSBbb3B0aW9ucy5fX3NoaW1UcmFuc2Zvcm1zX19dXG4gICAqIEBwYXJhbSB7T2JqZWN0fSBbb3B0aW9ucy5nbG9iYWxMZXhpY2Fsc11cbiAgICovXG5cbiAgLyoqXG4gICAqIEBjYWxsYmFjayBNYWtlQ29tcGFydG1lbnRDb25zdHJ1Y3RvclxuICAgKiBAcGFyYW0ge01ha2VDb21wYXJ0bWVudENvbnN0cnVjdG9yfSB0YXJnZXRNYWtlQ29tcGFydG1lbnRDb25zdHJ1Y3RvclxuICAgKiBAcGFyYW0ge09iamVjdH0gaW50cmluc2ljc1xuICAgKiBAcGFyYW0geyhvYmplY3Q6IE9iamVjdCkgPT4gdm9pZH0gbmF0aXZlQnJhbmRlclxuICAgKiBAcmV0dXJucyB7Q29tcGFydG1lbnRDb25zdHJ1Y3Rvcn1cbiAgICovXG5cbiAgLyoqIEB0eXBlIHtNYWtlQ29tcGFydG1lbnRDb25zdHJ1Y3Rvcn0gKi9cbiAgY29uc3QgbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3IgPSAoXG4gICAgdGFyZ2V0TWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3IsXG4gICAgaW50cmluc2ljcyxcbiAgICBuYXRpdmVCcmFuZGVyLFxuICApID0+IHtcbiAgICAvKiogQHR5cGUge0NvbXBhcnRtZW50Q29uc3RydWN0b3J9ICovXG4gICAgZnVuY3Rpb24gQ29tcGFydG1lbnQoZW5kb3dtZW50cyA9IHt9LCBfbW9kdWxlTWFwID0ge30sIG9wdGlvbnMgPSB7fSkge1xuICAgICAgaWYgKG5ldy50YXJnZXQgPT09IHVuZGVmaW5lZCkge1xuICAgICAgICB0aHJvdyBuZXcgVHlwZUVycm9yKFxuICAgICAgICAgIFwiQ2xhc3MgY29uc3RydWN0b3IgQ29tcGFydG1lbnQgY2Fubm90IGJlIGludm9rZWQgd2l0aG91dCAnbmV3J1wiLFxuICAgICAgICApO1xuICAgICAgfVxuXG4gICAgICAvLyBFeHRyYWN0IG9wdGlvbnMsIGFuZCBzaGFsbG93LWNsb25lIHRyYW5zZm9ybXMuXG4gICAgICBjb25zdCB7XG4gICAgICAgIG5hbWUgPSAnPHVua25vd24+JyxcbiAgICAgICAgdHJhbnNmb3JtcyA9IFtdLFxuICAgICAgICBfX3NoaW1UcmFuc2Zvcm1zX18gPSBbXSxcbiAgICAgICAgZ2xvYmFsTGV4aWNhbHMgPSB7fSxcbiAgICAgIH0gPSBvcHRpb25zO1xuICAgICAgY29uc3QgZ2xvYmFsVHJhbnNmb3JtcyA9IFsuLi50cmFuc2Zvcm1zLCAuLi5fX3NoaW1UcmFuc2Zvcm1zX19dO1xuXG4gICAgICBjb25zdCBnbG9iYWxPYmplY3QgPSB7fTtcbiAgICAgIGluaXRHbG9iYWxPYmplY3QoXG4gICAgICAgIGdsb2JhbE9iamVjdCxcbiAgICAgICAgaW50cmluc2ljcyxcbiAgICAgICAgc2hhcmVkR2xvYmFsUHJvcGVydHlOYW1lcyxcbiAgICAgICAgdGFyZ2V0TWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3IsXG4gICAgICAgIHRoaXMuY29uc3RydWN0b3IucHJvdG90eXBlLFxuICAgICAgICB7XG4gICAgICAgICAgZ2xvYmFsVHJhbnNmb3JtcyxcbiAgICAgICAgICBuYXRpdmVCcmFuZGVyLFxuICAgICAgICB9LFxuICAgICAgKTtcblxuICAgICAgYXNzaWduKGdsb2JhbE9iamVjdCwgZW5kb3dtZW50cyk7XG5cbiAgICAgIGNvbnN0IGludmFsaWROYW1lcyA9IGdldE93blByb3BlcnR5TmFtZXMoZ2xvYmFsTGV4aWNhbHMpLmZpbHRlcihcbiAgICAgICAgaWRlbnRpZmllciA9PiAhaXNWYWxpZElkZW50aWZpZXJOYW1lKGlkZW50aWZpZXIpLFxuICAgICAgKTtcbiAgICAgIGlmIChpbnZhbGlkTmFtZXMubGVuZ3RoKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcihcbiAgICAgICAgICBgQ2Fubm90IGNyZWF0ZSBjb21wYXJ0bWVudCB3aXRoIGludmFsaWQgbmFtZXMgZm9yIGdsb2JhbCBsZXhpY2FsczogJHtpbnZhbGlkTmFtZXMuam9pbihcbiAgICAgICAgICAnLCAnLFxuICAgICAgICApfTsgdGhlc2UgbmFtZXMgd291bGQgbm90IGJlIGxleGljYWxseSBtZW50aW9uYWJsZWAsXG4gICAgICAgICk7XG4gICAgICB9XG5cbiAgICAgIGNvbnN0IGtub3duU2NvcGVQcm94aWVzID0gbmV3IFdlYWtTZXQoKTtcbiAgICAgIHByaXZhdGVGaWVsZHMuc2V0KHRoaXMsIHtcbiAgICAgICAgbmFtZSxcbiAgICAgICAgZ2xvYmFsVHJhbnNmb3JtcyxcbiAgICAgICAgZ2xvYmFsT2JqZWN0LFxuICAgICAgICBrbm93blNjb3BlUHJveGllcyxcbiAgICAgICAgLy8gVGhlIGNhbGxlciBjb250aW51ZXMgdG8gb3duIHRoZSBnbG9iYWxMZXhpY2FscyBvYmplY3QgdGhleSBwYXNzZWQgdG9cbiAgICAgICAgLy8gdGhlIGNvbXBhcnRtZW50IGNvbnN0cnVjdG9yLCBidXQgdGhlIGNvbXBhcnRtZW50IG9ubHkgcmVzcGVjdHMgdGhlXG4gICAgICAgIC8vIG9yaWdpbmFsIHZhbHVlcyBhbmQgdGhleSBhcmUgY29uc3RhbnRzIGluIHRoZSBzY29wZSBvZiBldmFsdWF0ZWRcbiAgICAgICAgLy8gcHJvZ3JhbXMgYW5kIGV4ZWN1dGVkIG1vZHVsZXMuXG4gICAgICAgIC8vIFRoaXMgc2hhbGxvdyBjb3B5IGNhcHR1cmVzIG9ubHkgdGhlIHZhbHVlcyBvZiBlbnVtZXJhYmxlIG93blxuICAgICAgICAvLyBwcm9wZXJ0aWVzLCBlcmFzaW5nIGFjY2Vzc29ycy5cbiAgICAgICAgLy8gVGhlIHNuYXBzaG90IGlzIGZyb3plbiB0byBlbnN1cmUgdGhhdCB0aGUgcHJvcGVydGllcyBhcmUgaW1tdXRhYmxlXG4gICAgICAgIC8vIHdoZW4gdHJhbnNmZXJyZWQtYnktcHJvcGVydHktZGVzY3JpcHRvciBvbnRvIGxvY2FsIHNjb3BlIG9iamVjdHMuXG4gICAgICAgIGdsb2JhbExleGljYWxzOiBmcmVlemUoeyAuLi5nbG9iYWxMZXhpY2FscyB9KSxcbiAgICAgIH0pO1xuICAgIH1cblxuICAgIENvbXBhcnRtZW50LnByb3RvdHlwZSA9IENvbXBhcnRtZW50UHJvdG90eXBlO1xuXG4gICAgcmV0dXJuIENvbXBhcnRtZW50O1xuICB9O1xuXG4gIC8vIENvcHlyaWdodCAoQykgMjAxOCBBZ29yaWNcblxuICBjb25zdCBuYXRpdmVCcmFuZGVyJDEgPSB0YW1lRnVuY3Rpb25Ub1N0cmluZygpO1xuXG4gIGNvbnN0IENvbXBhcnRtZW50ID0gbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3IoXG4gICAgbWFrZUNvbXBhcnRtZW50Q29uc3RydWN0b3IsXG4gICAgZ2V0R2xvYmFsSW50cmluc2ljcyhnbG9iYWxUaGlzKSxcbiAgICBuYXRpdmVCcmFuZGVyJDEsXG4gICk7XG5cbiAgYXNzaWduKGdsb2JhbFRoaXMsIHtcbiAgICBoYXJkZW4sXG4gICAgbG9ja2Rvd246IG1ha2VMb2NrZG93bihcbiAgICAgIG1ha2VDb21wYXJ0bWVudENvbnN0cnVjdG9yLFxuICAgICAgQ29tcGFydG1lbnRQcm90b3R5cGUsXG4gICAgICBnZXRBbm9ueW1vdXNJbnRyaW5zaWNzLFxuICAgICksXG4gICAgQ29tcGFydG1lbnQsXG4gICAgYXNzZXJ0LFxuICB9KTtcblxufSkpKTtcblxuLy8gRU5EIG9mIGluamVjdGVkIGNvZGUgZnJvbSBzZXNcbiAgfSkoKVxuICByZXR1cm4gbW9kdWxlLmV4cG9ydHNcbn0pKClcblxuICAgIGNvbnN0IGxvY2tkb3duT3B0aW9ucyA9IHtcbiAgICAgIC8vIGdpdmVzIGEgc2VtaS1oaWdoIHJlc29sdXRpb24gdGltZXJcbiAgICAgIGRhdGVUYW1pbmc6ICd1bnNhZmUnLFxuICAgICAgLy8gdGhpcyBpcyBpbnRyb2R1Y2VzIG5vbi1kZXRlcm1pbmlzbSwgYnV0IGlzIG90aGVyd2lzZSBzYWZlXG4gICAgICBtYXRoVGFtaW5nOiAndW5zYWZlJyxcbiAgICAgIC8vIGxldHMgY29kZSBvYnNlcnZlIGNhbGwgc3RhY2ssIGJ1dCBlYXNpZXIgZGVidWdnYWJpbGl0eVxuICAgICAgZXJyb3JUYW1pbmc6ICd1bnNhZmUnLFxuICAgICAgLy8gc2hvd3MgdGhlIGZ1bGwgY2FsbCBzdGFja1xuICAgICAgc3RhY2tGaWx0ZXJpbmc6ICd2ZXJib3NlJyxcbiAgICB9XG5cbiAgICBsb2NrZG93bihsb2NrZG93bk9wdGlvbnMpXG5cbiAgICAvLyBpbml0aWFsaXplIHRoZSBrZXJuZWxcbiAgICBjb25zdCBjcmVhdGVLZXJuZWxDb3JlID0gKGZ1bmN0aW9uICgpIHtcbiAgcmV0dXJuIGNyZWF0ZUtlcm5lbFxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUtlcm5lbCAoe1xuICAgIC8vIHRoZSBwbGF0Zm9ybSBhcGkgZ2xvYmFsXG4gICAgZ2xvYmFsUmVmLFxuICAgIC8vIHBhY2thZ2UgcG9saWN5IG9iamVjdFxuICAgIGxhdmFtb2F0Q29uZmlnLFxuICAgIC8vIGtlcm5lbCBjb25maWd1cmF0aW9uXG4gICAgbG9hZE1vZHVsZURhdGEsXG4gICAgZ2V0UmVsYXRpdmVNb2R1bGVJZCxcbiAgICBwcmVwYXJlTW9kdWxlSW5pdGlhbGl6ZXJBcmdzLFxuICAgIGdldEV4dGVybmFsQ29tcGFydG1lbnQsXG4gICAgZ2xvYmFsVGhpc1JlZnMsXG4gICAgLy8gc2VjdXJpdHkgb3B0aW9uc1xuICAgIGRlYnVnTW9kZVxuICB9KSB7XG4gICAgLy8gY3JlYXRlIFNFUy13cmFwcGVkIExhdmFNb2F0IGtlcm5lbFxuICAgIC8vIGVuZG93bWVudHM6XG4gICAgLy8gLSBjb25zb2xlIGlzIGluY2x1ZGVkIGZvciBjb252ZW5pZW5jZVxuICAgIC8vIC0gTWF0aCBpcyBmb3IgdW50YW1lZCBNYXRoLnJhbmRvbVxuICAgIC8vIC0gRGF0ZSBpcyBmb3IgdW50YW1lZCBEYXRlLm5vd1xuICAgIGNvbnN0IGtlcm5lbENvbXBhcnRtZW50ID0gbmV3IENvbXBhcnRtZW50KHsgY29uc29sZSwgTWF0aCwgRGF0ZSB9KVxuICAgIGNvbnN0IG1ha2VLZXJuZWwgPSBrZXJuZWxDb21wYXJ0bWVudC5ldmFsdWF0ZShgKCR7dW5zYWZlQ3JlYXRlS2VybmVsfSlcXG4vLyMgc291cmNlVVJMPUxhdmFNb2F0L2NvcmUva2VybmVsYClcbiAgICBjb25zdCBsYXZhbW9hdEtlcm5lbCA9IG1ha2VLZXJuZWwoe1xuICAgICAgZ2xvYmFsUmVmLFxuICAgICAgbGF2YW1vYXRDb25maWcsXG4gICAgICBsb2FkTW9kdWxlRGF0YSxcbiAgICAgIGdldFJlbGF0aXZlTW9kdWxlSWQsXG4gICAgICBwcmVwYXJlTW9kdWxlSW5pdGlhbGl6ZXJBcmdzLFxuICAgICAgZ2V0RXh0ZXJuYWxDb21wYXJ0bWVudCxcbiAgICAgIGdsb2JhbFRoaXNSZWZzLFxuICAgICAgZGVidWdNb2RlXG4gICAgfSlcblxuICAgIHJldHVybiBsYXZhbW9hdEtlcm5lbFxuICB9XG5cbiAgLy8gdGhpcyBpcyBzZXJpYWxpemVkIGFuZCBydW4gaW4gU0VTXG4gIC8vIG1vc3RseSBqdXN0IGV4aXN0cyB0byBleHBvc2UgdmFyaWFibGVzIHRvIGludGVybmFsUmVxdWlyZSBhbmQgbG9hZEJ1bmRsZVxuICBmdW5jdGlvbiB1bnNhZmVDcmVhdGVLZXJuZWwgKHtcbiAgICBnbG9iYWxSZWYsXG4gICAgZGVidWdNb2RlLFxuICAgIGxhdmFtb2F0Q29uZmlnLFxuICAgIGxvYWRNb2R1bGVEYXRhLFxuICAgIGdldFJlbGF0aXZlTW9kdWxlSWQsXG4gICAgcHJlcGFyZU1vZHVsZUluaXRpYWxpemVyQXJncyxcbiAgICBnZXRFeHRlcm5hbENvbXBhcnRtZW50LFxuICAgIGdsb2JhbFRoaXNSZWZzID0gWydnbG9iYWxUaGlzJ11cbiAgfSkge1xuICAgIC8vIFwidGVtcGxhdGVSZXF1aXJlXCIgY2FsbHMgYXJlIGlubGluZWQgaW4gXCJnZW5lcmF0ZVByZWx1ZGVcIlxuICAgIGNvbnN0IGdlbmVyYWxVdGlscyA9IC8vIGRlZmluZSBtYWtlR2VuZXJhbFV0aWxzXG4oZnVuY3Rpb24oKXtcbiAgY29uc3QgZ2xvYmFsID0gZ2xvYmFsUmVmXG4gIGNvbnN0IGV4cG9ydHMgPSB7fVxuICBjb25zdCBtb2R1bGUgPSB7IGV4cG9ydHMgfVxuICA7KGZ1bmN0aW9uKCl7XG4vLyBTVEFSVCBvZiBpbmplY3RlZCBjb2RlIGZyb20gbWFrZUdlbmVyYWxVdGlsc1xubW9kdWxlLmV4cG9ydHMgPSBtYWtlR2VuZXJhbFV0aWxzXG5cbmZ1bmN0aW9uIG1ha2VHZW5lcmFsVXRpbHMgKCkge1xuICByZXR1cm4ge1xuICAgIGNyZWF0ZUZ1bmN0aW9uV3JhcHBlclxuICB9XG5cbiAgZnVuY3Rpb24gY3JlYXRlRnVuY3Rpb25XcmFwcGVyIChzb3VyY2VWYWx1ZSwgdW53cmFwVGVzdCwgdW53cmFwVG8pIHtcbiAgICBjb25zdCBuZXdWYWx1ZSA9IGZ1bmN0aW9uICguLi5hcmdzKSB7XG4gICAgICBpZiAobmV3LnRhcmdldCkge1xuICAgICAgICAvLyBoYW5kbGUgY29uc3RydWN0b3IgY2FsbHNcbiAgICAgICAgcmV0dXJuIFJlZmxlY3QuY29uc3RydWN0KHNvdXJjZVZhbHVlLCBhcmdzLCBuZXcudGFyZ2V0KVxuICAgICAgfSBlbHNlIHtcbiAgICAgICAgLy8gaGFuZGxlIGZ1bmN0aW9uIGNhbGxzXG4gICAgICAgIC8vIHVud3JhcCB0byB0YXJnZXQgdmFsdWUgaWYgdGhpcyB2YWx1ZSBpcyB0aGUgc291cmNlIHBhY2thZ2UgY29tcGFydG1lbnQncyBnbG9iYWxUaGlzXG4gICAgICAgIGNvbnN0IHRoaXNSZWYgPSB1bndyYXBUZXN0KHRoaXMpID8gdW53cmFwVG8gOiB0aGlzXG4gICAgICAgIHJldHVybiBSZWZsZWN0LmFwcGx5KHNvdXJjZVZhbHVlLCB0aGlzUmVmLCBhcmdzKVxuICAgICAgfVxuICAgIH1cbiAgICBPYmplY3QuZGVmaW5lUHJvcGVydGllcyhuZXdWYWx1ZSwgT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcnMoc291cmNlVmFsdWUpKVxuICAgIHJldHVybiBuZXdWYWx1ZVxuICB9XG59XG4vLyBFTkQgb2YgaW5qZWN0ZWQgY29kZSBmcm9tIG1ha2VHZW5lcmFsVXRpbHNcbiAgfSkoKVxuICByZXR1cm4gbW9kdWxlLmV4cG9ydHNcbn0pKCkoKVxuICAgIGNvbnN0IHsgZ2V0RW5kb3dtZW50c0ZvckNvbmZpZywgbWFrZU1pbmltYWxWaWV3T2ZSZWYsIGFwcGx5RW5kb3dtZW50UHJvcERlc2NUcmFuc2Zvcm1zIH0gPSAvLyBkZWZpbmUgbWFrZUdldEVuZG93bWVudHNGb3JDb25maWdcbihmdW5jdGlvbigpe1xuICBjb25zdCBnbG9iYWwgPSBnbG9iYWxSZWZcbiAgY29uc3QgZXhwb3J0cyA9IHt9XG4gIGNvbnN0IG1vZHVsZSA9IHsgZXhwb3J0cyB9XG4gIDsoZnVuY3Rpb24oKXtcbi8vIFNUQVJUIG9mIGluamVjdGVkIGNvZGUgZnJvbSBtYWtlR2V0RW5kb3dtZW50c0ZvckNvbmZpZ1xuLy8gdGhlIGNvbnRlbnRzIG9mIHRoaXMgZmlsZSB3aWxsIGJlIGNvcGllZCBpbnRvIHRoZSBwcmVsdWRlIHRlbXBsYXRlXG4vLyB0aGlzIG1vZHVsZSBoYXMgYmVlbiB3cml0dGVuIHNvIHRoYXQgaXQgcmVxdWlyZWQgZGlyZWN0bHkgb3IgY29waWVkIGFuZCBhZGRlZCB0byB0aGUgdGVtcGxhdGUgd2l0aCBhIHNtYWxsIHdyYXBwZXJcbm1vZHVsZS5leHBvcnRzID0gbWFrZUdldEVuZG93bWVudHNGb3JDb25maWdcblxuLy8gdXRpbGl0aWVzIGZvciBnZW5lcmF0aW5nIHRoZSBlbmRvd21lbnRzIG9iamVjdCBiYXNlZCBvbiBhIGdsb2JhbFJlZiBhbmQgYSBjb25maWdcblxuLy8gVGhlIGNvbmZpZyB1c2VzIGEgcGVyaW9kLWRlbGltaW5hdGVkIHBhdGggbm90YXRpb24gdG8gcHVsbCBvdXQgZGVlcCB2YWx1ZXMgZnJvbSBvYmplY3RzXG4vLyBUaGVzZSB1dGlsaXRpZXMgaGVscCBjcmVhdGUgYW4gb2JqZWN0IHBvcHVsYXRlZCB3aXRoIG9ubHkgdGhlIGRlZXAgcHJvcGVydGllcyBzcGVjaWZpZWQgaW4gdGhlIGNvbmZpZ1xuXG5mdW5jdGlvbiBtYWtlR2V0RW5kb3dtZW50c0ZvckNvbmZpZyAoeyBjcmVhdGVGdW5jdGlvbldyYXBwZXIgfSkge1xuICByZXR1cm4ge1xuICAgIGdldEVuZG93bWVudHNGb3JDb25maWcsXG4gICAgbWFrZU1pbmltYWxWaWV3T2ZSZWYsXG4gICAgY29weVZhbHVlQXRQYXRoLFxuICAgIGFwcGx5R2V0U2V0UHJvcERlc2NUcmFuc2Zvcm1zLFxuICAgIGFwcGx5RW5kb3dtZW50UHJvcERlc2NUcmFuc2Zvcm1zXG4gIH1cblxuICAvKipcbiAgICpcbiAgICogQGZ1bmN0aW9uIGdldEVuZG93bWVudHNGb3JDb25maWdcbiAgICogQHBhcmFtIHtvYmplY3R9IHNvdXJjZVJlZiAtIE9iamVjdCBmcm9tIHdoaWNoIHRvIGNvcHkgcHJvcGVydGllc1xuICAgKiBAcGFyYW0ge29iamVjdH0gY29uZmlnIC0gTGF2YU1vYXQgcGFja2FnZSBjb25maWdcbiAgICogQHBhcmFtIHtvYmplY3R9IHVud3JhcFRvIC0gRm9yIGdldHRlcnMgYW5kIHNldHRlcnMsIHdoZW4gdGhlIHRoaXMtdmFsdWUgaXMgdW53cmFwRnJvbSwgaXMgcmVwbGFjZWQgYXMgdW53cmFwVG9cbiAgICogQHBhcmFtIHtvYmplY3R9IHVud3JhcEZyb20gLSBGb3IgZ2V0dGVycyBhbmQgc2V0dGVycywgdGhlIHRoaXMtdmFsdWUgdG8gcmVwbGFjZSAoZGVmYXVsdDogdGFyZ2V0UmVmKVxuICAgKiBAcmV0dXJuIHtvYmplY3R9IC0gVGhlIHRhcmdldFJlZlxuICAgKlxuICAgKi9cbiAgZnVuY3Rpb24gZ2V0RW5kb3dtZW50c0ZvckNvbmZpZyAoc291cmNlUmVmLCBjb25maWcsIHVud3JhcFRvLCB1bndyYXBGcm9tKSB7XG4gICAgaWYgKCFjb25maWcuZ2xvYmFscykgcmV0dXJuIHt9XG4gICAgLy8gdmFsaWRhdGUgcmVhZCBhY2Nlc3MgZnJvbSBjb25maWdcbiAgICBjb25zdCB3aGl0ZWxpc3RlZFJlYWRzID0gW11cbiAgICBPYmplY3QuZW50cmllcyhjb25maWcuZ2xvYmFscykuZm9yRWFjaCgoW3BhdGgsIGNvbmZpZ1ZhbHVlXSkgPT4ge1xuICAgICAgY29uc3QgcGF0aFBhcnRzID0gcGF0aC5zcGxpdCgnLicpXG4gICAgICAvLyBkaXNhbGxvdyBkdW5kZXIgcHJvdG8gaW4gcGF0aFxuICAgICAgY29uc3QgcGF0aENvbnRhaW5zRHVuZGVyUHJvdG8gPSBwYXRoUGFydHMuc29tZShwYXRoUGFydCA9PiBwYXRoUGFydCA9PT0gJ19fcHJvdG9fXycpXG4gICAgICBpZiAocGF0aENvbnRhaW5zRHVuZGVyUHJvdG8pIHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKGBMYXZhbW9hdCAtIFwiX19wcm90b19fXCIgZGlzYWxsb3dlZCB3aGVuIGNyZWF0aW5nIG1pbmlhbCB2aWV3LiBzYXcgXCIke3BhdGh9XCJgKVxuICAgICAgfVxuICAgICAgLy8gd3JpdGUgYWNjZXNzIGhhbmRsZWQgZWxzZXdoZXJlXG4gICAgICBpZiAoY29uZmlnVmFsdWUgPT09ICd3cml0ZScpIHJldHVyblxuICAgICAgaWYgKGNvbmZpZ1ZhbHVlICE9PSB0cnVlKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcihgTGF2YU1vYXQgLSB1bmtub3duIHZhbHVlIGZvciBjb25maWcgKCR7dHlwZW9mIGNvbmZpZ1ZhbHVlfSlgKVxuICAgICAgfVxuICAgICAgd2hpdGVsaXN0ZWRSZWFkcy5wdXNoKHBhdGgpXG4gICAgfSlcbiAgICByZXR1cm4gbWFrZU1pbmltYWxWaWV3T2ZSZWYoc291cmNlUmVmLCB3aGl0ZWxpc3RlZFJlYWRzLCB1bndyYXBUbywgdW53cmFwRnJvbSlcbiAgfVxuXG4gIGZ1bmN0aW9uIG1ha2VNaW5pbWFsVmlld09mUmVmIChzb3VyY2VSZWYsIHBhdGhzLCB1bndyYXBUbywgdW53cmFwRnJvbSkge1xuICAgIGNvbnN0IHRhcmdldFJlZiA9IHt9XG4gICAgcGF0aHMuZm9yRWFjaChwYXRoID0+IHtcbiAgICAgIGNvcHlWYWx1ZUF0UGF0aChwYXRoLnNwbGl0KCcuJyksIHNvdXJjZVJlZiwgdGFyZ2V0UmVmLCB1bndyYXBUbywgdW53cmFwRnJvbSlcbiAgICB9KVxuICAgIHJldHVybiB0YXJnZXRSZWZcbiAgfVxuXG4gIGZ1bmN0aW9uIGNvcHlWYWx1ZUF0UGF0aCAocGF0aFBhcnRzLCBzb3VyY2VSZWYsIHRhcmdldFJlZiwgdW53cmFwVG8gPSBzb3VyY2VSZWYsIHVud3JhcEZyb20gPSB0YXJnZXRSZWYpIHtcbiAgICBpZiAocGF0aFBhcnRzLmxlbmd0aCA9PT0gMCkge1xuICAgICAgdGhyb3cgbmV3IEVycm9yKCd1bmFibGUgdG8gY29weSwgbXVzdCBoYXZlIHBhdGhQYXJ0cywgd2FzIGVtcHR5JylcbiAgICB9XG4gICAgY29uc3QgW25leHRQYXJ0LCAuLi5yZW1haW5pbmdQYXJ0c10gPSBwYXRoUGFydHNcbiAgICAvLyBnZXQgdGhlIHByb3BlcnR5IGZyb20gYW55IGRlcHRoIGluIHRoZSBwcm9wZXJ0eSBjaGFpblxuICAgIGNvbnN0IHsgcHJvcDogc291cmNlUHJvcERlc2MgfSA9IGdldFByb3BlcnR5RGVzY3JpcHRvckRlZXAoc291cmNlUmVmLCBuZXh0UGFydClcblxuICAgIC8vIGlmIHNvdXJjZSBtaXNzaW5nIHRoZSB2YWx1ZSB0byBjb3B5LCBqdXN0IHNraXAgaXRcbiAgICBpZiAoIXNvdXJjZVByb3BEZXNjKSB7XG4gICAgICByZXR1cm5cbiAgICB9XG5cbiAgICAvLyBpZiB0YXJnZXQgYWxyZWFkeSBoYXMgYSB2YWx1ZSwgaXQgbXVzdCBiZSBleHRlbnNpYmxlXG4gICAgY29uc3QgdGFyZ2V0UHJvcERlc2MgPSBSZWZsZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcih0YXJnZXRSZWYsIG5leHRQYXJ0KVxuICAgIGlmICh0YXJnZXRQcm9wRGVzYykge1xuICAgICAgLy8gZG9udCBhdHRlbXB0IHRvIGV4dGVuZCBhIGdldHRlciBvciB0cmlnZ2VyIGEgc2V0dGVyXG4gICAgICBpZiAoISgndmFsdWUnIGluIHRhcmdldFByb3BEZXNjKSkge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoYHVuYWJsZSB0byBjb3B5IG9uIHRvIHRhcmdldFJlZiwgdGFyZ2V0UmVmIGhhcyBhIGdldHRlciBhdCBcIiR7bmV4dFBhcnR9XCJgKVxuICAgICAgfVxuICAgICAgLy8gdmFsdWUgbXVzdCBiZSBleHRlbnNpYmxlIChjYW50IHdyaXRlIHByb3BlcnRpZXMgb250byBpdClcbiAgICAgIGNvbnN0IHRhcmdldFZhbHVlID0gdGFyZ2V0UHJvcERlc2MudmFsdWVcbiAgICAgIGNvbnN0IHZhbHVlVHlwZSA9IHR5cGVvZiB0YXJnZXRWYWx1ZVxuICAgICAgaWYgKHZhbHVlVHlwZSAhPT0gJ29iamVjdCcgJiYgdmFsdWVUeXBlICE9PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgIHRocm93IG5ldyBFcnJvcihgdW5hYmxlIHRvIGNvcHkgb24gdG8gdGFyZ2V0UmVmLCB0YXJnZXRSZWYgdmFsdWUgaXMgbm90IGFuIG9iaiBvciBmdW5jIFwiJHtuZXh0UGFydH1cImApXG4gICAgICB9XG4gICAgfVxuXG4gICAgLy8gaWYgdGhpcyBpcyBub3QgdGhlIGxhc3QgcGF0aCBpbiB0aGUgYXNzaWdubWVudCwgd2FsayBpbnRvIHRoZSBjb250YWluaW5nIHJlZmVyZW5jZVxuICAgIGlmIChyZW1haW5pbmdQYXJ0cy5sZW5ndGggPiAwKSB7XG4gICAgICBjb25zdCB7IHNvdXJjZVZhbHVlLCBzb3VyY2VXcml0YWJsZSB9ID0gZ2V0U291cmNlVmFsdWUoKVxuICAgICAgY29uc3QgbmV4dFNvdXJjZVJlZiA9IHNvdXJjZVZhbHVlXG4gICAgICBsZXQgbmV4dFRhcmdldFJlZlxuICAgICAgLy8gY2hlY2sgaWYgdmFsdWUgZXhpc3RzIG9uIHRhcmdldFxuICAgICAgaWYgKHRhcmdldFByb3BEZXNjKSB7XG4gICAgICAgIC8vIGEgdmFsdWUgYWxyZWFkeSBleGlzdHMsIHdlIHNob3VsZCB3YWxrIGludG8gaXRcbiAgICAgICAgbmV4dFRhcmdldFJlZiA9IHRhcmdldFByb3BEZXNjLnZhbHVlXG4gICAgICB9IGVsc2Uge1xuICAgICAgICAvLyBpdHMgbm90IHBvcHVsYXRlZCBzbyBsZXRzIHdyaXRlIHRvIGl0XG4gICAgICAgIC8vIHB1dCBhbiBvYmplY3QgdG8gc2VydmUgYXMgYSBjb250YWluZXJcbiAgICAgICAgY29uc3QgY29udGFpbmVyUmVmID0ge31cbiAgICAgICAgY29uc3QgbmV3UHJvcERlc2MgPSB7XG4gICAgICAgICAgdmFsdWU6IGNvbnRhaW5lclJlZixcbiAgICAgICAgICB3cml0YWJsZTogc291cmNlV3JpdGFibGUsXG4gICAgICAgICAgZW51bWVyYWJsZTogc291cmNlUHJvcERlc2MuZW51bWVyYWJsZSxcbiAgICAgICAgICBjb25maWd1cmFibGU6IHNvdXJjZVByb3BEZXNjLmNvbmZpZ3VyYWJsZVxuICAgICAgICB9XG4gICAgICAgIFJlZmxlY3QuZGVmaW5lUHJvcGVydHkodGFyZ2V0UmVmLCBuZXh0UGFydCwgbmV3UHJvcERlc2MpXG4gICAgICAgIC8vIHRoZSBuZXdseSBjcmVhdGVkIGNvbnRhaW5lciB3aWxsIGJlIHRoZSBuZXh0IHRhcmdldFxuICAgICAgICBuZXh0VGFyZ2V0UmVmID0gY29udGFpbmVyUmVmXG4gICAgICB9XG4gICAgICBjb3B5VmFsdWVBdFBhdGgocmVtYWluaW5nUGFydHMsIG5leHRTb3VyY2VSZWYsIG5leHRUYXJnZXRSZWYpXG4gICAgICByZXR1cm5cbiAgICB9XG5cbiAgICAvLyB0aGlzIGlzIHRoZSBsYXN0IHBhcnQgb2YgdGhlIHBhdGgsIHRoZSB2YWx1ZSB3ZSdyZSB0cnlpbmcgdG8gYWN0dWFsbHkgY29weVxuICAgIC8vIGlmIGhhcyBnZXR0ZXIvc2V0dGVyIC0gYXBwbHkgdGhpcy12YWx1ZSB1bndyYXBwaW5nXG4gICAgaWYgKCEoJ3ZhbHVlJyBpbiBzb3VyY2VQcm9wRGVzYykpIHtcbiAgICAgIC8vIHdyYXBwZXIgc2V0dGVyL2dldHRlciB3aXRoIGNvcnJlY3QgcmVjZWl2ZXJcbiAgICAgIGNvbnN0IHdyYXBwZXJQcm9wRGVzYyA9IGFwcGx5R2V0U2V0UHJvcERlc2NUcmFuc2Zvcm1zKHNvdXJjZVByb3BEZXNjLCB1bndyYXBGcm9tLCB1bndyYXBUbylcbiAgICAgIFJlZmxlY3QuZGVmaW5lUHJvcGVydHkodGFyZ2V0UmVmLCBuZXh0UGFydCwgd3JhcHBlclByb3BEZXNjKVxuICAgICAgcmV0dXJuXG4gICAgfVxuXG4gICAgLy8gbmVlZCB0byBkZXRlcm1pbmUgdGhlIHZhbHVlIHR5cGUgaW4gb3JkZXIgdG8gY29weSBpdCB3aXRoXG4gICAgLy8gdGhpcy12YWx1ZSB1bndyYXBwaW5nIHN1cHBvcnRcbiAgICBjb25zdCB7IHNvdXJjZVZhbHVlLCBzb3VyY2VXcml0YWJsZSB9ID0gZ2V0U291cmNlVmFsdWUoKVxuXG4gICAgLy8gbm90IGEgZnVuY3Rpb24gLSBjb3B5IGFzIGlzXG4gICAgaWYgKHR5cGVvZiBzb3VyY2VWYWx1ZSAhPT0gJ2Z1bmN0aW9uJykge1xuICAgICAgUmVmbGVjdC5kZWZpbmVQcm9wZXJ0eSh0YXJnZXRSZWYsIG5leHRQYXJ0LCBzb3VyY2VQcm9wRGVzYylcbiAgICAgIHJldHVyblxuICAgIH1cbiAgICAvLyBvdGhlcndpc2UgYWRkIHdvcmthcm91bmQgZm9yIGZ1bmN0aW9ucyB0byBzd2FwIGJhY2sgdG8gdGhlIHNvdXJjZWFsIFwidGhpc1wiIHJlZmVyZW5jZVxuICAgIGNvbnN0IHVud3JhcFRlc3QgPSB0aGlzVmFsdWUgPT4gdGhpc1ZhbHVlID09PSB1bndyYXBGcm9tXG4gICAgY29uc3QgbmV3VmFsdWUgPSBjcmVhdGVGdW5jdGlvbldyYXBwZXIoc291cmNlVmFsdWUsIHVud3JhcFRlc3QsIHVud3JhcFRvKVxuICAgIGNvbnN0IG5ld1Byb3BEZXNjID0ge1xuICAgICAgdmFsdWU6IG5ld1ZhbHVlLFxuICAgICAgd3JpdGFibGU6IHNvdXJjZVdyaXRhYmxlLFxuICAgICAgZW51bWVyYWJsZTogc291cmNlUHJvcERlc2MuZW51bWVyYWJsZSxcbiAgICAgIGNvbmZpZ3VyYWJsZTogc291cmNlUHJvcERlc2MuY29uZmlndXJhYmxlXG4gICAgfVxuICAgIFJlZmxlY3QuZGVmaW5lUHJvcGVydHkodGFyZ2V0UmVmLCBuZXh0UGFydCwgbmV3UHJvcERlc2MpXG5cbiAgICBmdW5jdGlvbiBnZXRTb3VyY2VWYWx1ZSAoKSB7XG4gICAgICAvLyBkZXRlcm1pbmUgdGhlIHNvdXJjZSB2YWx1ZSwgdGhpcyBjb2VyY2VzIGdldHRlcnMgdG8gdmFsdWVzXG4gICAgICAvLyBpbSBkZWVwbHkgc29ycnksIHJlc3BlY3RpbmcgZ2V0dGVycyB3YXMgY29tcGxpY2F0ZWQgYW5kXG4gICAgICAvLyBteSBicmFpbiBpcyBub3QgdmVyeSBnb29kXG4gICAgICBsZXQgc291cmNlVmFsdWUsIHNvdXJjZVdyaXRhYmxlXG4gICAgICBpZiAoJ3ZhbHVlJyBpbiBzb3VyY2VQcm9wRGVzYykge1xuICAgICAgICBzb3VyY2VWYWx1ZSA9IHNvdXJjZVByb3BEZXNjLnZhbHVlXG4gICAgICAgIHNvdXJjZVdyaXRhYmxlID0gc291cmNlUHJvcERlc2Mud3JpdGFibGVcbiAgICAgIH0gZWxzZSBpZiAoJ2dldCcgaW4gc291cmNlUHJvcERlc2MpIHtcbiAgICAgICAgc291cmNlVmFsdWUgPSBzb3VyY2VQcm9wRGVzYy5nZXQuY2FsbCh1bndyYXBUbylcbiAgICAgICAgc291cmNlV3JpdGFibGUgPSAnc2V0JyBpbiBzb3VyY2VQcm9wRGVzY1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdnZXRFbmRvd21lbnRzRm9yQ29uZmlnIC0gcHJvcGVydHkgZGVzY3JpcHRvciBtaXNzaW5nIGEgZ2V0dGVyJylcbiAgICAgIH1cbiAgICAgIHJldHVybiB7IHNvdXJjZVZhbHVlLCBzb3VyY2VXcml0YWJsZSB9XG4gICAgfVxuICB9XG5cbiAgZnVuY3Rpb24gYXBwbHlFbmRvd21lbnRQcm9wRGVzY1RyYW5zZm9ybXMgKHByb3BEZXNjLCB1bndyYXBGcm9tQ29tcGFydG1lbnQsIHVud3JhcFRvR2xvYmFsVGhpcykge1xuICAgIGxldCBuZXdQcm9wRGVzYyA9IHByb3BEZXNjXG4gICAgbmV3UHJvcERlc2MgPSBhcHBseUZ1bmN0aW9uUHJvcERlc2NUcmFuc2Zvcm0obmV3UHJvcERlc2MsIHVud3JhcEZyb21Db21wYXJ0bWVudCwgdW53cmFwVG9HbG9iYWxUaGlzKVxuICAgIG5ld1Byb3BEZXNjID0gYXBwbHlHZXRTZXRQcm9wRGVzY1RyYW5zZm9ybXMobmV3UHJvcERlc2MsIHVud3JhcEZyb21Db21wYXJ0bWVudC5nbG9iYWxUaGlzLCB1bndyYXBUb0dsb2JhbFRoaXMpXG4gICAgcmV0dXJuIG5ld1Byb3BEZXNjXG4gIH1cblxuICBmdW5jdGlvbiBhcHBseUdldFNldFByb3BEZXNjVHJhbnNmb3JtcyAoc291cmNlUHJvcERlc2MsIHVud3JhcEZyb21HbG9iYWxUaGlzLCB1bndyYXBUb0dsb2JhbFRoaXMpIHtcbiAgICBjb25zdCB3cmFwcGVkUHJvcERlc2MgPSB7IC4uLnNvdXJjZVByb3BEZXNjIH1cbiAgICBpZiAoc291cmNlUHJvcERlc2MuZ2V0KSB7XG4gICAgICB3cmFwcGVkUHJvcERlc2MuZ2V0ID0gZnVuY3Rpb24gKCkge1xuICAgICAgICBjb25zdCByZWNlaXZlciA9IHRoaXNcbiAgICAgICAgLy8gcmVwbGFjZSB0aGUgXCJyZWNlaXZlclwiIHZhbHVlIGlmIGl0IHBvaW50cyB0byBmYWtlIHBhcmVudFxuICAgICAgICBjb25zdCByZWNlaXZlclJlZiA9IHJlY2VpdmVyID09PSB1bndyYXBGcm9tR2xvYmFsVGhpcyA/IHVud3JhcFRvR2xvYmFsVGhpcyA6IHJlY2VpdmVyXG4gICAgICAgIC8vIHNvbWV0aW1lcyBnZXR0ZXJzIHJlcGxhY2UgdGhlbXNlbHZlcyB3aXRoIHN0YXRpYyBwcm9wZXJ0aWVzLCBhcyBzZWVuIHdpaCB0aGUgRmlyZUZveCBydW50aW1lXG4gICAgICAgIGNvbnN0IHJlc3VsdCA9IFJlZmxlY3QuYXBwbHkoc291cmNlUHJvcERlc2MuZ2V0LCByZWNlaXZlclJlZiwgW10pXG4gICAgICAgIGlmICh0eXBlb2YgcmVzdWx0ID09PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgICAgLy8gZnVuY3Rpb25zIG11c3QgYmUgd3JhcHBlZCB0byBlbnN1cmUgYSBnb29kIHRoaXMtdmFsdWUuXG4gICAgICAgICAgLy8gbG9ja2Rvd24gY2F1c2VzIHNvbWUgcHJvcERlc2NzIHRvIGdvIHRvIHZhbHVlIC0+IGdldHRlcixcbiAgICAgICAgICAvLyBlZyBcIkZ1bmN0aW9uLnByb3RvdHlwZS5iaW5kXCIuIHdlIG5lZWQgdG8gd3JhcCBnZXR0ZXIgcmVzdWx0c1xuICAgICAgICAgIC8vIGFzIHdlbGwgaW4gb3JkZXIgdG8gZW5zdXJlIHRoZXkgaGF2ZSB0aGVpciB0aGlzLXZhbHVlIHdyYXBwZWQgY29ycmVjdGx5XG4gICAgICAgICAgLy8gaWYgdGhpcyBlbmRzIHVwIGJlaW5nIHByb2JsZW1hdGljIHdlIGNhbiBtYXliZSB0YWtlIGFkdmFudGFnZSBvZiBsb2NrZG93bidzXG4gICAgICAgICAgLy8gXCJnZXR0ZXIub3JpZ2luYWxWYWx1ZVwiIHByb3BlcnR5IGJlaW5nIGF2YWlsYWJsZVxuICAgICAgICAgIHJldHVybiBjcmVhdGVGdW5jdGlvbldyYXBwZXIocmVzdWx0LCAodGhpc1ZhbHVlKSA9PiB0aGlzVmFsdWUgPT09IHVud3JhcEZyb21HbG9iYWxUaGlzLCB1bndyYXBUb0dsb2JhbFRoaXMpXG4gICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgcmV0dXJuIHJlc3VsdFxuICAgICAgICB9XG4gICAgICB9XG4gICAgfVxuICAgIGlmIChzb3VyY2VQcm9wRGVzYy5zZXQpIHtcbiAgICAgIHdyYXBwZWRQcm9wRGVzYy5zZXQgPSBmdW5jdGlvbiAodmFsdWUpIHtcbiAgICAgICAgLy8gcmVwbGFjZSB0aGUgXCJyZWNlaXZlclwiIHZhbHVlIGlmIGl0IHBvaW50cyB0byBmYWtlIHBhcmVudFxuICAgICAgICBjb25zdCByZWNlaXZlciA9IHRoaXNcbiAgICAgICAgY29uc3QgcmVjZWl2ZXJSZWYgPSByZWNlaXZlciA9PT0gdW53cmFwRnJvbUdsb2JhbFRoaXMgPyB1bndyYXBUb0dsb2JhbFRoaXMgOiByZWNlaXZlclxuICAgICAgICByZXR1cm4gUmVmbGVjdC5hcHBseShzb3VyY2VQcm9wRGVzYy5zZXQsIHJlY2VpdmVyUmVmLCBbdmFsdWVdKVxuICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gd3JhcHBlZFByb3BEZXNjXG4gIH1cblxuICBmdW5jdGlvbiBhcHBseUZ1bmN0aW9uUHJvcERlc2NUcmFuc2Zvcm0gKHByb3BEZXNjLCB1bndyYXBGcm9tQ29tcGFydG1lbnQsIHVud3JhcFRvR2xvYmFsVGhpcykge1xuICAgIGlmICghKCd2YWx1ZScgaW4gcHJvcERlc2MgJiYgdHlwZW9mIHByb3BEZXNjLnZhbHVlID09PSAnZnVuY3Rpb24nKSkge1xuICAgICAgcmV0dXJuIHByb3BEZXNjXG4gICAgfVxuICAgIGNvbnN0IHVud3JhcFRlc3QgPSAodGhpc1ZhbHVlKSA9PiB7XG4gICAgICAvLyB1bndyYXAgZnVuY3Rpb24gY2FsbHMgdGhpcy12YWx1ZSB0byB1bndyYXBUb0dsb2JhbFRoaXMgd2hlbjpcbiAgICAgIC8vIHRoaXMgdmFsdWUgaXMgZ2xvYmFsVGhpcyBleC4gZ2xvYmFsVGhpcy5hYmMoKVxuICAgICAgLy8gc2NvcGUgcHJveHkgbGVhayB3b3JrYXJvdW5kIGV4LiBhYmMoKVxuICAgICAgcmV0dXJuIHRoaXNWYWx1ZSA9PT0gdW53cmFwRnJvbUNvbXBhcnRtZW50Lmdsb2JhbFRoaXMgfHwgdW53cmFwRnJvbUNvbXBhcnRtZW50Ll9faXNLbm93blNjb3BlUHJveHlfXyh0aGlzVmFsdWUpXG4gICAgfVxuICAgIGNvbnN0IG5ld0ZuID0gY3JlYXRlRnVuY3Rpb25XcmFwcGVyKHByb3BEZXNjLnZhbHVlLCB1bndyYXBUZXN0LCB1bndyYXBUb0dsb2JhbFRoaXMpXG4gICAgcmV0dXJuIHsgLi4ucHJvcERlc2MsIHZhbHVlOiBuZXdGbiB9XG4gIH1cbn1cblxuZnVuY3Rpb24gZ2V0UHJvcGVydHlEZXNjcmlwdG9yRGVlcCAodGFyZ2V0LCBrZXkpIHtcbiAgbGV0IHJlY2VpdmVyID0gdGFyZ2V0XG4gIHdoaWxlICh0cnVlKSB7XG4gICAgLy8gc3VwcG9ydCBsb29rdXAgb24gb2JqZWN0cyBhbmQgcHJpbWl0aXZlc1xuICAgIGNvbnN0IHR5cGVvZlJlY2VpdmVyID0gdHlwZW9mIHJlY2VpdmVyXG4gICAgaWYgKHR5cGVvZlJlY2VpdmVyID09PSAnb2JqZWN0JyB8fCB0eXBlb2ZSZWNlaXZlciA9PT0gJ2Z1bmN0aW9uJykge1xuICAgICAgY29uc3QgcHJvcCA9IFJlZmxlY3QuZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKHJlY2VpdmVyLCBrZXkpXG4gICAgICBpZiAocHJvcCkge1xuICAgICAgICByZXR1cm4geyByZWNlaXZlciwgcHJvcCB9XG4gICAgICB9XG4gICAgICAvLyB0cnkgbmV4dCBpbiB0aGUgcHJvdG90eXBlIGNoYWluXG4gICAgICByZWNlaXZlciA9IFJlZmxlY3QuZ2V0UHJvdG90eXBlT2YocmVjZWl2ZXIpXG4gICAgfSBlbHNlIHtcbiAgICAgIC8vIHByb3RvdHlwZSBsb29rdXAgZm9yIHByaW1pdGl2ZXNcbiAgICAgIC8vIGVzbGludC1kaXNhYmxlLW5leHQtbGluZSBuby1wcm90b1xuICAgICAgcmVjZWl2ZXIgPSByZWNlaXZlci5fX3Byb3RvX19cbiAgICB9XG4gICAgLy8gYWJvcnQgaWYgdGhpcyBpcyB0aGUgZW5kIG9mIHRoZSBwcm90b3R5cGUgY2hhaW4uXG4gICAgaWYgKCFyZWNlaXZlcikgcmV0dXJuIHsgcHJvcDogbnVsbCwgcmVjZWl2ZXI6IG51bGwgfVxuICB9XG59XG5cbi8vIEVORCBvZiBpbmplY3RlZCBjb2RlIGZyb20gbWFrZUdldEVuZG93bWVudHNGb3JDb25maWdcbiAgfSkoKVxuICByZXR1cm4gbW9kdWxlLmV4cG9ydHNcbn0pKCkoZ2VuZXJhbFV0aWxzKVxuICAgIGNvbnN0IHsgcHJlcGFyZUNvbXBhcnRtZW50R2xvYmFsRnJvbUNvbmZpZyB9ID0gLy8gZGVmaW5lIG1ha2VQcmVwYXJlUmVhbG1HbG9iYWxGcm9tQ29uZmlnXG4oZnVuY3Rpb24oKXtcbiAgY29uc3QgZ2xvYmFsID0gZ2xvYmFsUmVmXG4gIGNvbnN0IGV4cG9ydHMgPSB7fVxuICBjb25zdCBtb2R1bGUgPSB7IGV4cG9ydHMgfVxuICA7KGZ1bmN0aW9uKCl7XG4vLyBTVEFSVCBvZiBpbmplY3RlZCBjb2RlIGZyb20gbWFrZVByZXBhcmVSZWFsbUdsb2JhbEZyb21Db25maWdcbi8vIHRoZSBjb250ZW50cyBvZiB0aGlzIGZpbGUgd2lsbCBiZSBjb3BpZWQgaW50byB0aGUgcHJlbHVkZSB0ZW1wbGF0ZVxuLy8gdGhpcyBtb2R1bGUgaGFzIGJlZW4gd3JpdHRlbiBzbyB0aGF0IGl0IHJlcXVpcmVkIGRpcmVjdGx5IG9yIGNvcGllZCBhbmQgYWRkZWQgdG8gdGhlIHRlbXBsYXRlIHdpdGggYSBzbWFsbCB3cmFwcGVyXG5tb2R1bGUuZXhwb3J0cyA9IG1ha2VQcmVwYXJlUmVhbG1HbG9iYWxGcm9tQ29uZmlnXG5cbi8vIHV0aWxpdGllcyBmb3IgZXhwb3NpbmcgY29uZmlndXJpbmcgdGhlIGV4cG9zZWQgZW5kb3dtZW50cyBvbiB0aGUgY29udGFpbmVyIGdsb2JhbFxuXG4vLyBUaGUgY29uZmlnIHVzZXMgYSBwZXJpb2QtZGVsaW1pbmF0ZWQgcGF0aCBub3RhdGlvbiB0byBwdWxsIG91dCBkZWVwIHZhbHVlcyBmcm9tIG9iamVjdHNcbi8vIFRoZXNlIHV0aWxpdGllcyBoZWxwIG1vZGlmeSB0aGUgY29udGFpbmVyIGdsb2JhbCB0byBleHBvc2UgdGhlIGFsbG93ZWQgZ2xvYmFscyBmcm9tIHRoZSBnbG9iYWxTdG9yZSBPUiB0aGUgcGxhdGZvcm0gZ2xvYmFsXG5cbmZ1bmN0aW9uIG1ha2VQcmVwYXJlUmVhbG1HbG9iYWxGcm9tQ29uZmlnICh7IGNyZWF0ZUZ1bmN0aW9uV3JhcHBlciB9KSB7XG4gIHJldHVybiB7XG4gICAgcHJlcGFyZUNvbXBhcnRtZW50R2xvYmFsRnJvbUNvbmZpZyxcbiAgICBnZXRUb3BMZXZlbFJlYWRBY2Nlc3NGcm9tUGFja2FnZUNvbmZpZyxcbiAgICBnZXRUb3BMZXZlbFdyaXRlQWNjZXNzRnJvbVBhY2thZ2VDb25maWdcbiAgfVxuXG4gIGZ1bmN0aW9uIGdldFRvcExldmVsUmVhZEFjY2Vzc0Zyb21QYWNrYWdlQ29uZmlnIChnbG9iYWxzQ29uZmlnKSB7XG4gICAgY29uc3QgcmVzdWx0ID0gT2JqZWN0LmVudHJpZXMoZ2xvYmFsc0NvbmZpZylcbiAgICAgIC5maWx0ZXIoKFtrZXksIHZhbHVlXSkgPT4gdmFsdWUgPT09ICdyZWFkJyB8fCB2YWx1ZSA9PT0gdHJ1ZSB8fCAodmFsdWUgPT09ICd3cml0ZScgJiYga2V5LnNwbGl0KCcuJykubGVuZ3RoID4gMSkpXG4gICAgICAubWFwKChba2V5XSkgPT4ga2V5LnNwbGl0KCcuJylbMF0pXG4gICAgLy8gcmV0dXJuIHVuaXF1ZSBhcnJheVxuICAgIHJldHVybiBBcnJheS5mcm9tKG5ldyBTZXQocmVzdWx0KSlcbiAgfVxuXG4gIGZ1bmN0aW9uIGdldFRvcExldmVsV3JpdGVBY2Nlc3NGcm9tUGFja2FnZUNvbmZpZyAoZ2xvYmFsc0NvbmZpZykge1xuICAgIGNvbnN0IHJlc3VsdCA9IE9iamVjdC5lbnRyaWVzKGdsb2JhbHNDb25maWcpXG4gICAgICAuZmlsdGVyKChba2V5LCB2YWx1ZV0pID0+IHZhbHVlID09PSAnd3JpdGUnICYmIGtleS5zcGxpdCgnLicpLmxlbmd0aCA9PT0gMSlcbiAgICAgIC5tYXAoKFtrZXldKSA9PiBrZXkpXG4gICAgcmV0dXJuIHJlc3VsdFxuICB9XG5cbiAgZnVuY3Rpb24gcHJlcGFyZUNvbXBhcnRtZW50R2xvYmFsRnJvbUNvbmZpZyAocGFja2FnZUNvbXBhcnRtZW50LCBnbG9iYWxzQ29uZmlnLCBlbmRvd21lbnRzLCBnbG9iYWxTdG9yZSwgZ2xvYmFsVGhpc1JlZnMpIHtcbiAgICBjb25zdCBwYWNrYWdlQ29tcGFydG1lbnRHbG9iYWwgPSBwYWNrYWdlQ29tcGFydG1lbnQuZ2xvYmFsVGhpc1xuICAgIC8vIGxvb2t1cCB0b3AgbGV2ZWwgcmVhZCArIHdyaXRlIGFjY2VzcyBrZXlzXG4gICAgY29uc3QgdG9wTGV2ZWxXcml0ZUFjY2Vzc0tleXMgPSBnZXRUb3BMZXZlbFdyaXRlQWNjZXNzRnJvbVBhY2thZ2VDb25maWcoZ2xvYmFsc0NvbmZpZylcbiAgICBjb25zdCB0b3BMZXZlbFJlYWRBY2Nlc3NLZXlzID0gZ2V0VG9wTGV2ZWxSZWFkQWNjZXNzRnJvbVBhY2thZ2VDb25maWcoZ2xvYmFsc0NvbmZpZylcblxuICAgIC8vIGRlZmluZSBhY2Nlc3NvcnNcblxuICAgIC8vIGFsbG93IHJlYWQgYWNjZXNzIHZpYSBnbG9iYWxTdG9yZSBvciBwYWNrYWdlQ29tcGFydG1lbnRHbG9iYWxcbiAgICB0b3BMZXZlbFJlYWRBY2Nlc3NLZXlzLmZvckVhY2goa2V5ID0+IHtcbiAgICAgIE9iamVjdC5kZWZpbmVQcm9wZXJ0eShwYWNrYWdlQ29tcGFydG1lbnRHbG9iYWwsIGtleSwge1xuICAgICAgICBnZXQgKCkge1xuICAgICAgICAgIGlmIChnbG9iYWxTdG9yZS5oYXMoa2V5KSkge1xuICAgICAgICAgICAgcmV0dXJuIGdsb2JhbFN0b3JlLmdldChrZXkpXG4gICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHJldHVybiBSZWZsZWN0LmdldChlbmRvd21lbnRzLCBrZXksIHRoaXMpXG4gICAgICAgICAgfVxuICAgICAgICB9LFxuICAgICAgICBzZXQgKCkge1xuICAgICAgICAgIC8vIFRPRE86IHRoZXJlIHNob3VsZCBiZSBhIGNvbmZpZyB0byB0aHJvdyB2cyBzaWxlbnRseSBpZ25vcmVcbiAgICAgICAgICBjb25zb2xlLndhcm4oYExhdmFNb2F0OiBpZ25vcmluZyB3cml0ZSBhdHRlbXB0IHRvIHJlYWQtYWNjZXNzIGdsb2JhbCBcIiR7a2V5fVwiYClcbiAgICAgICAgfVxuICAgICAgfSlcbiAgICB9KVxuXG4gICAgLy8gYWxsb3cgd3JpdGUgYWNjZXNzIHRvIGdsb2JhbFN0b3JlXG4gICAgLy8gcmVhZCBhY2Nlc3MgdmlhIGdsb2JhbFN0b3JlIG9yIHBhY2thZ2VDb21wYXJ0bWVudEdsb2JhbFxuICAgIHRvcExldmVsV3JpdGVBY2Nlc3NLZXlzLmZvckVhY2goa2V5ID0+IHtcbiAgICAgIE9iamVjdC5kZWZpbmVQcm9wZXJ0eShwYWNrYWdlQ29tcGFydG1lbnRHbG9iYWwsIGtleSwge1xuICAgICAgICBnZXQgKCkge1xuICAgICAgICAgIGlmIChnbG9iYWxTdG9yZS5oYXMoa2V5KSkge1xuICAgICAgICAgICAgcmV0dXJuIGdsb2JhbFN0b3JlLmdldChrZXkpXG4gICAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICAgIHJldHVybiBlbmRvd21lbnRzW2tleV1cbiAgICAgICAgICB9XG4gICAgICAgIH0sXG4gICAgICAgIHNldCAodmFsdWUpIHtcbiAgICAgICAgICBnbG9iYWxTdG9yZS5zZXQoa2V5LCB2YWx1ZSlcbiAgICAgICAgfSxcbiAgICAgICAgZW51bWVyYWJsZTogdHJ1ZSxcbiAgICAgICAgY29uZmlndXJhYmxlOiB0cnVlXG4gICAgICB9KVxuICAgIH0pXG5cbiAgICAvLyBzZXQgY2lyY3VsYXIgZ2xvYmFsUmVmc1xuICAgIGdsb2JhbFRoaXNSZWZzLmZvckVhY2goa2V5ID0+IHtcbiAgICAgIC8vIGlmIGdsb2JhbFJlZiBpcyBhY3R1YWxseSBhbiBlbmRvd21lbnQsIGlnbm9yZVxuICAgICAgaWYgKHRvcExldmVsUmVhZEFjY2Vzc0tleXMuaW5jbHVkZXMoa2V5KSkgcmV0dXJuXG4gICAgICBpZiAodG9wTGV2ZWxXcml0ZUFjY2Vzc0tleXMuaW5jbHVkZXMoa2V5KSkgcmV0dXJuXG4gICAgICAvLyBzZXQgY2lyY3VsYXIgcmVmIHRvIGdsb2JhbFxuICAgICAgcGFja2FnZUNvbXBhcnRtZW50R2xvYmFsW2tleV0gPSBwYWNrYWdlQ29tcGFydG1lbnRHbG9iYWxcbiAgICB9KVxuXG4gICAgLy8gYmluZCBGdW5jdGlvbiBjb25zdHJ1Y3RvciB0aGlzIHZhbHVlIHRvIGdsb2JhbFRoaXNcbiAgICAvLyBsZWdhY3kgZ2xvYmFsVGhpcyBzaGltXG4gICAgY29uc3Qgb3JpZ0Z1bmN0aW9uID0gcGFja2FnZUNvbXBhcnRtZW50R2xvYmFsLkZ1bmN0aW9uXG4gICAgY29uc3QgbmV3RnVuY3Rpb24gPSBmdW5jdGlvbiAoLi4uYXJncykge1xuICAgICAgY29uc3QgZm4gPSBvcmlnRnVuY3Rpb24oLi4uYXJncylcbiAgICAgIGNvbnN0IHVud3JhcFRlc3QgPSB0aGlzVmFsdWUgPT4gdGhpc1ZhbHVlID09PSB1bmRlZmluZWRcbiAgICAgIHJldHVybiBjcmVhdGVGdW5jdGlvbldyYXBwZXIoZm4sIHVud3JhcFRlc3QsIHBhY2thZ2VDb21wYXJ0bWVudEdsb2JhbClcbiAgICB9XG4gICAgT2JqZWN0LmRlZmluZVByb3BlcnRpZXMobmV3RnVuY3Rpb24sIE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3JzKG9yaWdGdW5jdGlvbikpXG4gICAgcGFja2FnZUNvbXBhcnRtZW50R2xvYmFsLkZ1bmN0aW9uID0gbmV3RnVuY3Rpb25cbiAgfVxufVxuXG4vLyBFTkQgb2YgaW5qZWN0ZWQgY29kZSBmcm9tIG1ha2VQcmVwYXJlUmVhbG1HbG9iYWxGcm9tQ29uZmlnXG4gIH0pKClcbiAgcmV0dXJuIG1vZHVsZS5leHBvcnRzXG59KSgpKGdlbmVyYWxVdGlscylcblxuICAgIGNvbnN0IG1vZHVsZUNhY2hlID0gbmV3IE1hcCgpXG4gICAgY29uc3QgcGFja2FnZUNvbXBhcnRtZW50Q2FjaGUgPSBuZXcgTWFwKClcbiAgICBjb25zdCBnbG9iYWxTdG9yZSA9IG5ldyBNYXAoKVxuXG4gICAgY29uc3Qgcm9vdFBhY2thZ2VOYW1lID0gJzxyb290PidcbiAgICBjb25zdCByb290UGFja2FnZUNvbXBhcnRtZW50ID0gY3JlYXRlUm9vdFBhY2thZ2VDb21wYXJ0bWVudChnbG9iYWxSZWYpXG5cbiAgICByZXR1cm4ge1xuICAgICAgaW50ZXJuYWxSZXF1aXJlXG4gICAgfVxuXG4gICAgLy8gdGhpcyBmdW5jdGlvbiBpbnN0YW50aWF0aWVzIGEgbW9kdWxlIGZyb20gYSBtb2R1bGVJZC5cbiAgICAvLyAxLiBsb2FkcyB0aGUgbW9kdWxlIG1ldGFkYXRhIGFuZCBwb2xpY3lcbiAgICAvLyAyLiBwcmVwYXJlcyB0aGUgZXhlY3V0aW9uIGVudmlyb25tZW50XG4gICAgLy8gMy4gaW5zdGFudGlhdGVzIHRoZSBtb2R1bGUsIHJlY3Vyc2l2ZWx5IGluc3RhbnRpYXRpbmcgZGVwZW5kZW5jaWVzXG4gICAgLy8gNC4gcmV0dXJucyB0aGUgbW9kdWxlIGV4cG9ydHNcbiAgICBmdW5jdGlvbiBpbnRlcm5hbFJlcXVpcmUgKG1vZHVsZUlkKSB7XG4gICAgICAvLyB1c2UgY2FjaGVkIG1vZHVsZS5leHBvcnRzIGlmIG1vZHVsZSBpcyBhbHJlYWR5IGluc3RhbnRpYXRlZFxuICAgICAgaWYgKG1vZHVsZUNhY2hlLmhhcyhtb2R1bGVJZCkpIHtcbiAgICAgICAgY29uc3QgbW9kdWxlRXhwb3J0cyA9IG1vZHVsZUNhY2hlLmdldChtb2R1bGVJZCkuZXhwb3J0c1xuICAgICAgICByZXR1cm4gbW9kdWxlRXhwb3J0c1xuICAgICAgfVxuXG4gICAgICAvLyBsb2FkIGFuZCB2YWxpZGF0ZSBtb2R1bGUgbWV0YWRhdGFcbiAgICAgIC8vIGlmIG1vZHVsZSBtZXRhZGF0YSBpcyBtaXNzaW5nLCB0aHJvdyBhbiBlcnJvclxuICAgICAgY29uc3QgbW9kdWxlRGF0YSA9IGxvYWRNb2R1bGVEYXRhKG1vZHVsZUlkKVxuICAgICAgaWYgKCFtb2R1bGVEYXRhKSB7XG4gICAgICAgIGNvbnN0IGVyciA9IG5ldyBFcnJvcignQ2Fubm90IGZpbmQgbW9kdWxlIFxcJycgKyBtb2R1bGVJZCArICdcXCcnKVxuICAgICAgICBlcnIuY29kZSA9ICdNT0RVTEVfTk9UX0ZPVU5EJ1xuICAgICAgICB0aHJvdyBlcnJcbiAgICAgIH1cbiAgICAgIGlmIChtb2R1bGVEYXRhLmlkID09PSB1bmRlZmluZWQpIHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKCdMYXZhTW9hdCAtIG1vZHVsZUlkIGlzIG5vdCBkZWZpbmVkIGNvcnJlY3RseS4nKVxuICAgICAgfVxuXG4gICAgICAvLyBwYXJzZSBhbmQgdmFsaWRhdGUgbW9kdWxlIGRhdGFcbiAgICAgIGNvbnN0IHsgcGFja2FnZTogcGFja2FnZU5hbWUsIHNvdXJjZTogbW9kdWxlU291cmNlIH0gPSBtb2R1bGVEYXRhXG4gICAgICBpZiAoIXBhY2thZ2VOYW1lKSB0aHJvdyBuZXcgRXJyb3IoYExhdmFNb2F0IC0gaW52YWxpZCBwYWNrYWdlTmFtZSBmb3IgbW9kdWxlIFwiJHttb2R1bGVJZH1cImApXG4gICAgICBjb25zdCBwYWNrYWdlUG9saWN5ID0gZ2V0UG9saWN5Rm9yUGFja2FnZShsYXZhbW9hdENvbmZpZywgcGFja2FnZU5hbWUpXG5cbiAgICAgIC8vIGNyZWF0ZSB0aGUgbW9kdWxlT2JqIGFuZCBpbml0aWFsaXplclxuICAgICAgY29uc3QgeyBtb2R1bGVJbml0aWFsaXplciwgbW9kdWxlT2JqIH0gPSBwcmVwYXJlTW9kdWxlSW5pdGlhbGl6ZXIobW9kdWxlRGF0YSwgcGFja2FnZVBvbGljeSlcblxuICAgICAgLy8gY2FjaGUgbW9kdWxlT2JqIGhlcmVcbiAgICAgIC8vIHRoaXMgaXMgaW1wb3J0YW50IHRvIGluZiBsb29wcyB3aGVuIGhpdHRpbmcgY3ljbGVzIGluIHRoZSBkZXAgZ3JhcGhcbiAgICAgIC8vIG11c3QgY2FjaGUgYmVmb3JlIHJ1bm5pbmcgdGhlIG1vZHVsZUluaXRpYWxpemVyXG4gICAgICBtb2R1bGVDYWNoZS5zZXQobW9kdWxlSWQsIG1vZHVsZU9iailcblxuICAgICAgLy8gdmFsaWRhdGUgbW9kdWxlSW5pdGlhbGl6ZXJcbiAgICAgIGlmICh0eXBlb2YgbW9kdWxlSW5pdGlhbGl6ZXIgIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKGBMYXZhTW9hdCAtIG1vZHVsZUluaXRpYWxpemVyIGlzIG5vdCBkZWZpbmVkIGNvcnJlY3RseS4gZ290IFwiJHt0eXBlb2YgbW9kdWxlSW5pdGlhbGl6ZXJ9XCJcXG4ke21vZHVsZVNvdXJjZX1gKVxuICAgICAgfVxuXG4gICAgICAvLyBpbml0aWFsaXplIHRoZSBtb2R1bGUgd2l0aCB0aGUgY29ycmVjdCBjb250ZXh0XG4gICAgICBjb25zdCBpbml0aWFsaXplckFyZ3MgPSBwcmVwYXJlTW9kdWxlSW5pdGlhbGl6ZXJBcmdzKHJlcXVpcmVSZWxhdGl2ZVdpdGhDb250ZXh0LCBtb2R1bGVPYmosIG1vZHVsZURhdGEpXG4gICAgICBtb2R1bGVJbml0aWFsaXplci5hcHBseShtb2R1bGVPYmouZXhwb3J0cywgaW5pdGlhbGl6ZXJBcmdzKVxuICAgICAgY29uc3QgbW9kdWxlRXhwb3J0cyA9IG1vZHVsZU9iai5leHBvcnRzXG5cbiAgICAgIHJldHVybiBtb2R1bGVFeHBvcnRzXG5cbiAgICAgIC8vIHRoaXMgaXMgcGFzc2VkIHRvIHRoZSBtb2R1bGUgaW5pdGlhbGl6ZXJcbiAgICAgIC8vIGl0IGFkZHMgdGhlIGNvbnRleHQgb2YgdGhlIHBhcmVudCBtb2R1bGVcbiAgICAgIC8vIHRoaXMgY291bGQgYmUgcmVwbGFjZWQgdmlhIFwiRnVuY3Rpb24ucHJvdG90eXBlLmJpbmRcIiBpZiBpdHMgbW9yZSBwZXJmb3JtYW50XG4gICAgICBmdW5jdGlvbiByZXF1aXJlUmVsYXRpdmVXaXRoQ29udGV4dCAocmVxdWVzdGVkTmFtZSkge1xuICAgICAgICBjb25zdCBwYXJlbnRNb2R1bGVFeHBvcnRzID0gbW9kdWxlT2JqLmV4cG9ydHNcbiAgICAgICAgY29uc3QgcGFyZW50TW9kdWxlRGF0YSA9IG1vZHVsZURhdGFcbiAgICAgICAgY29uc3QgcGFyZW50UGFja2FnZVBvbGljeSA9IHBhY2thZ2VQb2xpY3lcbiAgICAgICAgY29uc3QgcGFyZW50TW9kdWxlSWQgPSBtb2R1bGVJZFxuICAgICAgICByZXR1cm4gcmVxdWlyZVJlbGF0aXZlKHsgcmVxdWVzdGVkTmFtZSwgcGFyZW50TW9kdWxlRXhwb3J0cywgcGFyZW50TW9kdWxlRGF0YSwgcGFyZW50UGFja2FnZVBvbGljeSwgcGFyZW50TW9kdWxlSWQgfSlcbiAgICAgIH1cbiAgICB9XG5cbiAgICAvLyB0aGlzIHJlc29sdmVzIGEgbW9kdWxlIGdpdmVuIGEgcmVxdWVzdGVkTmFtZSAoZWcgcmVsYXRpdmUgcGF0aCB0byBwYXJlbnQpIGFuZCBhIHBhcmVudE1vZHVsZSBjb250ZXh0XG4gICAgLy8gdGhlIGV4cG9ydHMgYXJlIHByb2Nlc3NlZCB2aWEgXCJwcm90ZWN0RXhwb3J0c1JlcXVpcmVUaW1lXCIgcGVyIHRoZSBtb2R1bGUncyBjb25maWd1cmF0aW9uXG4gICAgZnVuY3Rpb24gcmVxdWlyZVJlbGF0aXZlICh7IHJlcXVlc3RlZE5hbWUsIHBhcmVudE1vZHVsZUV4cG9ydHMsIHBhcmVudE1vZHVsZURhdGEsIHBhcmVudFBhY2thZ2VQb2xpY3ksIHBhcmVudE1vZHVsZUlkIH0pIHtcbiAgICAgIGNvbnN0IHBhcmVudE1vZHVsZVBhY2thZ2VOYW1lID0gcGFyZW50TW9kdWxlRGF0YS5wYWNrYWdlXG4gICAgICBjb25zdCBwYXJlbnRQYWNrYWdlc1doaXRlbGlzdCA9IHBhcmVudFBhY2thZ2VQb2xpY3kucGFja2FnZXNcbiAgICAgIGNvbnN0IHBhcmVudEJ1aWx0aW5zV2hpdGVsaXN0ID0gT2JqZWN0LmVudHJpZXMocGFyZW50UGFja2FnZVBvbGljeS5idWlsdGluKVxuICAgICAgICAuZmlsdGVyKChbXywgYWxsb3dlZF0pID0+IGFsbG93ZWQgPT09IHRydWUpXG4gICAgICAgIC5tYXAoKFtwYWNrYWdlUGF0aCwgYWxsb3dlZF0pID0+IHBhY2thZ2VQYXRoLnNwbGl0KCcuJylbMF0pXG5cbiAgICAgIC8vIHJlc29sdmUgdGhlIG1vZHVsZUlkIGZyb20gdGhlIHJlcXVlc3RlZE5hbWVcbiAgICAgIGNvbnN0IG1vZHVsZUlkID0gZ2V0UmVsYXRpdmVNb2R1bGVJZChwYXJlbnRNb2R1bGVJZCwgcmVxdWVzdGVkTmFtZSlcblxuICAgICAgLy8gYnJvd3NlcmlmeSBnb29wOlxuICAgICAgLy8gcmVjdXJzaXZlIHJlcXVpcmVzIGRvbnQgaGl0IGNhY2hlIHNvIGl0IGluZiBsb29wcywgc28gd2Ugc2hvcnRjaXJjdWl0XG4gICAgICAvLyB0aGlzIG9ubHkgc2VlbXMgdG8gaGFwcGVuIHdpdGggYSBmZXcgYnJvd3NlcmlmeSBidWlsdGlucyAobm9kZWpzIGJ1aWx0aW4gbW9kdWxlIHBvbHlmaWxscylcbiAgICAgIC8vIHdlIGNvdWxkIGxpa2VseSBhbGxvdyBhbnkgcmVxdWVzdGVkTmFtZSBzaW5jZSBpdCBjYW4gb25seSByZWZlciB0byBpdHNlbGZcbiAgICAgIGlmIChtb2R1bGVJZCA9PT0gcGFyZW50TW9kdWxlSWQpIHtcbiAgICAgICAgaWYgKFsndGltZXJzJywgJ2J1ZmZlciddLmluY2x1ZGVzKHJlcXVlc3RlZE5hbWUpID09PSBmYWxzZSkge1xuICAgICAgICAgIHRocm93IG5ldyBFcnJvcihgTGF2YU1vYXQgLSByZWN1cnNpdmUgcmVxdWlyZSBkZXRlY3RlZDogXCIke3JlcXVlc3RlZE5hbWV9XCJgKVxuICAgICAgICB9XG4gICAgICAgIHJldHVybiBwYXJlbnRNb2R1bGVFeHBvcnRzXG4gICAgICB9XG5cbiAgICAgIC8vIGxvYWQgbW9kdWxlXG4gICAgICBsZXQgbW9kdWxlRXhwb3J0cyA9IGludGVybmFsUmVxdWlyZShtb2R1bGVJZClcblxuICAgICAgLy8gbG9vayB1cCBjb25maWcgZm9yIG1vZHVsZVxuICAgICAgY29uc3QgbW9kdWxlRGF0YSA9IGxvYWRNb2R1bGVEYXRhKG1vZHVsZUlkKVxuICAgICAgY29uc3QgcGFja2FnZU5hbWUgPSBtb2R1bGVEYXRhLnBhY2thZ2VcblxuICAgICAgLy8gZGlzYWxsb3cgcmVxdWlyaW5nIHBhY2thZ2VzIHRoYXQgYXJlIG5vdCBpbiB0aGUgcGFyZW50J3Mgd2hpdGVsaXN0XG4gICAgICBjb25zdCBpc1NhbWVQYWNrYWdlID0gcGFja2FnZU5hbWUgPT09IHBhcmVudE1vZHVsZVBhY2thZ2VOYW1lXG4gICAgICBjb25zdCBwYXJlbnRJc0VudHJ5TW9kdWxlID0gcGFyZW50TW9kdWxlUGFja2FnZU5hbWUgPT09IHJvb3RQYWNrYWdlTmFtZVxuICAgICAgbGV0IGlzSW5QYXJlbnRXaGl0ZWxpc3QgPSBmYWxzZVxuICAgICAgaWYgKG1vZHVsZURhdGEudHlwZSA9PT0gJ2J1aWx0aW4nKSB7XG4gICAgICAgIGlzSW5QYXJlbnRXaGl0ZWxpc3QgPSBwYXJlbnRCdWlsdGluc1doaXRlbGlzdC5pbmNsdWRlcyhwYWNrYWdlTmFtZSlcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGlzSW5QYXJlbnRXaGl0ZWxpc3QgPSAocGFyZW50UGFja2FnZXNXaGl0ZWxpc3RbcGFja2FnZU5hbWVdID09PSB0cnVlKVxuICAgICAgfVxuXG4gICAgICAvLyB2YWxpZGF0ZSB0aGF0IHRoZSBpbXBvcnQgaXMgYWxsb3dlZFxuICAgICAgaWYgKCFwYXJlbnRJc0VudHJ5TW9kdWxlICYmICFpc1NhbWVQYWNrYWdlICYmICFpc0luUGFyZW50V2hpdGVsaXN0KSB7XG4gICAgICAgIGxldCB0eXBlVGV4dCA9ICcgJ1xuICAgICAgICBpZiAobW9kdWxlRGF0YS50eXBlID09PSAnYnVpbHRpbicpIHR5cGVUZXh0ID0gJyBub2RlIGJ1aWx0aW4gJ1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoYExhdmFNb2F0IC0gcmVxdWlyZWQke3R5cGVUZXh0fXBhY2thZ2Ugbm90IGluIHdoaXRlbGlzdDogcGFja2FnZSBcIiR7cGFyZW50TW9kdWxlUGFja2FnZU5hbWV9XCIgcmVxdWVzdGVkIFwiJHtwYWNrYWdlTmFtZX1cIiBhcyBcIiR7cmVxdWVzdGVkTmFtZX1cImApXG4gICAgICB9XG5cbiAgICAgIC8vIGNyZWF0ZSBtaW5pbWFsIHNlbGVjdGlvbiBpZiBpdHMgYSBidWlsdGluIGFuZCB0aGUgd2hvbGUgcGF0aCBpcyBub3Qgc2VsZWN0ZWQgZm9yXG4gICAgICBpZiAoIXBhcmVudElzRW50cnlNb2R1bGUgJiYgbW9kdWxlRGF0YS50eXBlID09PSAnYnVpbHRpbicgJiYgIXBhcmVudFBhY2thZ2VQb2xpY3kuYnVpbHRpblttb2R1bGVJZF0pIHtcbiAgICAgICAgY29uc3QgYnVpbHRpblBhdGhzID0gKFxuICAgICAgICAgIE9iamVjdC5lbnRyaWVzKHBhcmVudFBhY2thZ2VQb2xpY3kuYnVpbHRpbilcbiAgICAgICAgICAvLyBncmFiIGFsbCBhbGxvd2VkIGJ1aWx0aW4gcGF0aHMgdGhhdCBtYXRjaCB0aGlzIHBhY2thZ2VcbiAgICAgICAgICAgIC5maWx0ZXIoKFtwYWNrYWdlUGF0aCwgYWxsb3dlZF0pID0+IGFsbG93ZWQgPT09IHRydWUgJiYgbW9kdWxlSWQgPT09IHBhY2thZ2VQYXRoLnNwbGl0KCcuJylbMF0pXG4gICAgICAgICAgLy8gb25seSBpbmNsdWRlIHRoZSBwYXRocyBhZnRlciB0aGUgcGFja2FnZU5hbWVcbiAgICAgICAgICAgIC5tYXAoKFtwYWNrYWdlUGF0aCwgYWxsb3dlZF0pID0+IHBhY2thZ2VQYXRoLnNwbGl0KCcuJykuc2xpY2UoMSkuam9pbignLicpKVxuICAgICAgICAgICAgLnNvcnQoKVxuICAgICAgICApXG4gICAgICAgIG1vZHVsZUV4cG9ydHMgPSBtYWtlTWluaW1hbFZpZXdPZlJlZihtb2R1bGVFeHBvcnRzLCBidWlsdGluUGF0aHMpXG4gICAgICB9XG5cbiAgICAgIHJldHVybiBtb2R1bGVFeHBvcnRzXG4gICAgfVxuXG4gICAgZnVuY3Rpb24gcHJlcGFyZU1vZHVsZUluaXRpYWxpemVyIChtb2R1bGVEYXRhLCBwYWNrYWdlUG9saWN5KSB7XG4gICAgICBjb25zdCB7IG1vZHVsZUluaXRpYWxpemVyLCBwYWNrYWdlOiBwYWNrYWdlTmFtZSwgaWQ6IG1vZHVsZUlkLCBzb3VyY2U6IG1vZHVsZVNvdXJjZSB9ID0gbW9kdWxlRGF0YVxuXG4gICAgICAvLyBtb2R1bGVJbml0aWFsaXplciBtYXkgYmUgc2V0IGJ5IGxvYWRNb2R1bGVEYXRhIChlLmcuIGJ1aWx0aW4gKyBuYXRpdmUgbW9kdWxlcylcbiAgICAgIGlmIChtb2R1bGVJbml0aWFsaXplcikge1xuICAgICAgICAvLyBpZiBhbiBleHRlcm5hbCBtb2R1bGVJbml0aWFsaXplciBpcyBzZXQsIGVuc3VyZSBpdCBpcyBhbGxvd2VkXG4gICAgICAgIGlmIChtb2R1bGVEYXRhLnR5cGUgPT09ICduYXRpdmUnKSB7XG4gICAgICAgICAgLy8gZW5zdXJlIHBhY2thZ2UgaXMgYWxsb3dlZCB0byBoYXZlIG5hdGl2ZSBtb2R1bGVzXG4gICAgICAgICAgaWYgKHBhY2thZ2VQb2xpY3kubmF0aXZlICE9PSB0cnVlKSB7XG4gICAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoYExhdmFNb2F0IC0gXCJuYXRpdmVcIiBtb2R1bGUgdHlwZSBub3QgcGVybWl0dGVkIGZvciBwYWNrYWdlIFwiJHtwYWNrYWdlTmFtZX1cIiwgbW9kdWxlIFwiJHttb2R1bGVJZH1cImApXG4gICAgICAgICAgfVxuICAgICAgICB9IGVsc2UgaWYgKG1vZHVsZURhdGEudHlwZSAhPT0gJ2J1aWx0aW4nKSB7XG4gICAgICAgICAgLy8gYnVpbHRpbiBtb2R1bGUgdHlwZXMgZG9udCBoYXZlIHBvbGljeSBjb25maWd1cmF0aW9uc1xuICAgICAgICAgIC8vIGJ1dCB0aGUgcGFja2FnZXMgdGhhdCBjYW4gaW1wb3J0IHRoZW0gYXJlIGNvbnN0cmFpbmVkIGVsc2V3aGVyZVxuICAgICAgICAgIC8vIGhlcmUgd2UganVzdCBlbnN1cmUgdGhhdCB0aGUgbW9kdWxlIHR5cGUgaXMgdGhlIG9ubHkgb3RoZXIgdHlwZSB3aXRoIGEgZXh0ZXJuYWwgbW9kdWxlSW5pdGlhbGl6ZXJcbiAgICAgICAgICB0aHJvdyBuZXcgRXJyb3IoYExhdmFNb2F0IC0gaW52YWxpZCBleHRlcm5hbCBtb2R1bGVJbml0aWFsaXplciBmb3IgbW9kdWxlIHR5cGUgXCIke21vZHVsZURhdGEudHlwZX1cIiBpbiBwYWNrYWdlIFwiJHtwYWNrYWdlTmFtZX1cIiwgbW9kdWxlIFwiJHttb2R1bGVJZH1cImApXG4gICAgICAgIH1cbiAgICAgICAgLy8gbW9kdWxlT2JqIG11c3QgYmUgZnJvbSB0aGUgc2FtZSBSZWFsbSBhcyB0aGUgbW9kdWxlSW5pdGlhbGl6ZXJcbiAgICAgICAgLy8gaGVyZSB3ZSBhcmUgYXNzdW1pbmcgdGhlIHByb3ZpZGVkIG1vZHVsZUluaXRpYWxpemVyIGlzIGZyb20gdGhlIHNhbWUgUmVhbG0gYXMgdGhpcyBrZXJuZWxcbiAgICAgICAgY29uc3QgbW9kdWxlT2JqID0geyBleHBvcnRzOiB7fSB9XG4gICAgICAgIHJldHVybiB7IG1vZHVsZUluaXRpYWxpemVyLCBtb2R1bGVPYmogfVxuICAgICAgfVxuXG4gICAgICAvLyBzZXR1cCBpbml0aWFsaXplciBmcm9tIG1vZHVsZVNvdXJjZSBhbmQgY29tcGFydG1lbnQuXG4gICAgICAvLyBleGVjdXRlIGluIHBhY2thZ2UgY29tcGFydG1lbnQgd2l0aCBnbG9iYWxUaGlzIHBvcHVsYXRlZCBwZXIgcGFja2FnZSBwb2xpY3lcbiAgICAgIGNvbnN0IHBhY2thZ2VDb21wYXJ0bWVudCA9IGdldENvbXBhcnRtZW50Rm9yUGFja2FnZShwYWNrYWdlTmFtZSwgcGFja2FnZVBvbGljeSlcbiAgICAgIC8vIFRPRE86IG1vdmUgYWxsIHNvdXJjZSBtdXRhdGlvbnMgZWxzZXdoZXJlXG4gICAgICB0cnkge1xuICAgICAgICBjb25zdCBzb3VyY2VVUkwgPSBtb2R1bGVEYXRhLmZpbGUgfHwgYG1vZHVsZXMvJHttb2R1bGVJZH1gXG4gICAgICAgIGlmIChzb3VyY2VVUkwuaW5jbHVkZXMoJ1xcbicpKSB7XG4gICAgICAgICAgdGhyb3cgbmV3IEVycm9yKGBMYXZhTW9hdCAtIE5ld2xpbmVzIG5vdCBhbGxvd2VkIGluIGZpbGVuYW1lczogJHtKU09OLnN0cmluZ2lmeShzb3VyY2VVUkwpfWApXG4gICAgICAgIH1cbiAgICAgICAgLy8gbW9kdWxlT2JqIG11c3QgYmUgZnJvbSB0aGUgc2FtZSBSZWFsbSBhcyB0aGUgbW9kdWxlSW5pdGlhbGl6ZXJcbiAgICAgICAgLy8gdGhlIGRhcnQyanMgcnVudGltZSByZWxpZXMgb24gdGhpcyBmb3Igc29tZSByZWFzb25cbiAgICAgICAgY29uc3QgbW9kdWxlT2JqID0gcGFja2FnZUNvbXBhcnRtZW50LmV2YWx1YXRlKCcoeyBleHBvcnRzOiB7fSB9KScpXG4gICAgICAgIGNvbnN0IG1vZHVsZUluaXRpYWxpemVyID0gcGFja2FnZUNvbXBhcnRtZW50LmV2YWx1YXRlKGAke21vZHVsZVNvdXJjZX1cXG4vLyMgc291cmNlVVJMPSR7c291cmNlVVJMfWApXG4gICAgICAgIHJldHVybiB7IG1vZHVsZUluaXRpYWxpemVyLCBtb2R1bGVPYmogfVxuICAgICAgfSBjYXRjaCAoZXJyKSB7XG4gICAgICAgIGNvbnNvbGUud2FybihgTGF2YU1vYXQgLSBFcnJvciBldmFsdWF0aW5nIG1vZHVsZSBcIiR7bW9kdWxlSWR9XCIgZnJvbSBwYWNrYWdlIFwiJHtwYWNrYWdlTmFtZX1cIiBcXG4ke2Vyci5zdGFja31gKVxuICAgICAgICB0aHJvdyBlcnJcbiAgICAgIH1cbiAgICB9XG5cbiAgICBmdW5jdGlvbiBjcmVhdGVSb290UGFja2FnZUNvbXBhcnRtZW50IChnbG9iYWxSZWYpIHtcbiAgICAgIGlmIChwYWNrYWdlQ29tcGFydG1lbnRDYWNoZS5oYXMocm9vdFBhY2thZ2VOYW1lKSkge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoJ0xhdmFNb2F0IC0gY3JlYXRlUm9vdFBhY2thZ2VDb21wYXJ0bWVudCBjYWxsZWQgbW9yZSB0aGFuIG9uY2UnKVxuICAgICAgfVxuICAgICAgLy8gcHJlcGFyZSB0aGUgcm9vdCBwYWNrYWdlJ3MgU0VTIENvbXBhcnRtZW50XG4gICAgICAvLyBlbmRvd21lbnRzOlxuICAgICAgLy8gLSBNYXRoIGlzIGZvciB1bnRhbWVkIE1hdGgucmFuZG9tXG4gICAgICAvLyAtIERhdGUgaXMgZm9yIHVudGFtZWQgRGF0ZS5ub3dcbiAgICAgIGNvbnN0IHJvb3RQYWNrYWdlQ29tcGFydG1lbnQgPSBuZXcgQ29tcGFydG1lbnQoeyBNYXRoLCBEYXRlIH0pXG4gICAgICAvLyBmaW5kIHRoZSByZWxldmFudCBlbmRvd21lbnQgc291cmNlc1xuICAgICAgY29uc3QgZ2xvYmFsUHJvdG9DaGFpbiA9IGdldFByb3RvdHlwZUNoYWluKGdsb2JhbFJlZilcbiAgICAgIC8vIHRoZSBpbmRleCBmb3IgdGhlIGNvbW1vbiBwcm90b3R5cGFsIGFuY2VzdG9yLCBPYmplY3QucHJvdG90eXBlXG4gICAgICAvLyB0aGlzIHNob3VsZCBhbHdheXMgYmUgdGhlIGxhc3QgaW5kZXgsIGJ1dCB3ZSBjaGVjayBqdXN0IGluIGNhc2VcbiAgICAgIGNvbnN0IGNvbW1vblByb3RvdHlwZUluZGV4ID0gZ2xvYmFsUHJvdG9DaGFpbi5maW5kSW5kZXgoZ2xvYmFsUHJvdG9DaGFpbkVudHJ5ID0+IGdsb2JhbFByb3RvQ2hhaW5FbnRyeSA9PT0gT2JqZWN0LnByb3RvdHlwZSlcbiAgICAgIGlmIChjb21tb25Qcm90b3R5cGVJbmRleCA9PT0gLTEpIHRocm93IG5ldyBFcnJvcignTGF2YW1vYXQgLSB1bmFibGUgdG8gZmluZCBjb21tb24gcHJvdG90eXBlIGJldHdlZW4gQ29tcGFydG1lbnQgYW5kIGdsb2JhbFJlZicpXG4gICAgICAvLyB3ZSB3aWxsIGNvcHkgZW5kb3dtZW50cyBmcm9tIGFsbCBlbnRyaWVzIGluIHRoZSBwcm90b3R5cGUgY2hhaW4sIGV4Y2x1ZGluZyBPYmplY3QucHJvdG90eXBlXG4gICAgICBjb25zdCBlbmRvd21lbnRTb3VyY2VzID0gZ2xvYmFsUHJvdG9DaGFpbi5zbGljZSgwLCBjb21tb25Qcm90b3R5cGVJbmRleClcblxuICAgICAgLy8gY2FsbCBhbGwgZ2V0dGVycywgaW4gY2FzZSBvZiBiZWhhdmlvciBjaGFuZ2UgKHN1Y2ggYXMgd2l0aCBGaXJlRm94IGxhenkgZ2V0dGVycylcbiAgICAgIC8vIGNhbGwgb24gY29udGVudHMgb2YgZW5kb3dtZW50c1NvdXJjZXMgZGlyZWN0bHkgaW5zdGVhZCBvZiBpbiBuZXcgYXJyYXkgaW5zdGFuY2VzLiBJZiB0aGVyZSBpcyBhIGxhenkgZ2V0dGVyIGl0IG9ubHkgY2hhbmdlcyB0aGUgb3JpZ2luYWwgcHJvcCBkZXNjLlxuICAgICAgZW5kb3dtZW50U291cmNlcy5mb3JFYWNoKHNvdXJjZSA9PiB7XG4gICAgICAgIGNvbnN0IGRlc2NyaXB0b3JzID0gT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcnMoc291cmNlKVxuICAgICAgICBPYmplY3QudmFsdWVzKGRlc2NyaXB0b3JzKS5mb3JFYWNoKGRlc2MgPT4ge1xuICAgICAgICAgIGlmICgnZ2V0JyBpbiBkZXNjKSB7XG4gICAgICAgICAgICBSZWZsZWN0LmFwcGx5KGRlc2MuZ2V0LCBnbG9iYWxSZWYsIFtdKVxuICAgICAgICAgIH1cbiAgICAgICAgfSlcbiAgICAgIH0pXG5cbiAgICAgIGNvbnN0IGVuZG93bWVudFNvdXJjZURlc2NyaXB0b3JzID0gZW5kb3dtZW50U291cmNlcy5tYXAoZ2xvYmFsUHJvdG9DaGFpbkVudHJ5ID0+IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3JzKGdsb2JhbFByb3RvQ2hhaW5FbnRyeSkpXG4gICAgICAvLyBmbGF0dGVuIHByb3BEZXNjIGNvbGxlY3Rpb25zIHdpdGggcHJlY2VkZW5jZSBmb3IgZ2xvYmFsVGhpcy1lbmQgb2YgdGhlIHByb3RvdHlwZSBjaGFpblxuICAgICAgY29uc3QgZW5kb3dtZW50RGVzY3JpcHRvcnNGbGF0ID0gT2JqZWN0LmFzc2lnbihPYmplY3QuY3JlYXRlKG51bGwpLCAuLi5lbmRvd21lbnRTb3VyY2VEZXNjcmlwdG9ycy5yZXZlcnNlKCkpXG4gICAgICAvLyBleHBvc2UgYWxsIG93biBwcm9wZXJ0aWVzIG9mIGdsb2JhbFJlZiwgaW5jbHVkaW5nIG5vbi1lbnVtZXJhYmxlXG4gICAgICBPYmplY3QuZW50cmllcyhlbmRvd21lbnREZXNjcmlwdG9yc0ZsYXQpXG4gICAgICAgIC8vIGlnbm9yZSBwcm9wZXJ0aWVzIGFscmVhZHkgZGVmaW5lZCBvbiBjb21wYXJ0bWVudCBnbG9iYWxcbiAgICAgICAgLmZpbHRlcigoW2tleV0pID0+ICEoa2V5IGluIHJvb3RQYWNrYWdlQ29tcGFydG1lbnQuZ2xvYmFsVGhpcykpXG4gICAgICAgIC8vIGlnbm9yZSBjaXJjdWxhciBnbG9iYWxUaGlzIHJlZnNcbiAgICAgICAgLmZpbHRlcigoW2tleV0pID0+ICEoZ2xvYmFsVGhpc1JlZnMuaW5jbHVkZXMoa2V5KSkpXG4gICAgICAgIC8vIGRlZmluZSBwcm9wZXJ0eSBvbiBjb21wYXJ0bWVudCBnbG9iYWxcbiAgICAgICAgLmZvckVhY2goKFtrZXksIGRlc2NdKSA9PiB7XG4gICAgICAgICAgLy8gdW53cmFwIGZ1bmN0aW9ucywgc2V0dGVycy9nZXR0ZXJzICYgYXBwbHkgc2NvcGUgcHJveHkgd29ya2Fyb3VuZFxuICAgICAgICAgIGNvbnN0IHdyYXBwZWRQcm9wRGVzYyA9IGFwcGx5RW5kb3dtZW50UHJvcERlc2NUcmFuc2Zvcm1zKGRlc2MsIHJvb3RQYWNrYWdlQ29tcGFydG1lbnQsIGdsb2JhbFJlZilcbiAgICAgICAgICBSZWZsZWN0LmRlZmluZVByb3BlcnR5KHJvb3RQYWNrYWdlQ29tcGFydG1lbnQuZ2xvYmFsVGhpcywga2V5LCB3cmFwcGVkUHJvcERlc2MpXG4gICAgICAgIH0pXG4gICAgICAvLyBnbG9iYWwgY2lyY3VsYXIgcmVmZXJlbmNlcyBvdGhlcndpc2UgYWRkZWQgYnkgcHJlcGFyZUNvbXBhcnRtZW50R2xvYmFsRnJvbUNvbmZpZ1xuICAgICAgLy8gQWRkIGFsbCBjaXJjdWxhciByZWZzIHRvIHJvb3QgcGFja2FnZSBjb21wYXJ0bWVudCBnbG9iYWxUaGlzXG4gICAgICBmb3IgKGNvbnN0IHJlZiBvZiBnbG9iYWxUaGlzUmVmcykge1xuICAgICAgICBpZiAocmVmIGluIHJvb3RQYWNrYWdlQ29tcGFydG1lbnQuZ2xvYmFsVGhpcykge1xuICAgICAgICAgIGNvbnRpbnVlXG4gICAgICAgIH1cbiAgICAgICAgcm9vdFBhY2thZ2VDb21wYXJ0bWVudC5nbG9iYWxUaGlzW3JlZl0gPSByb290UGFja2FnZUNvbXBhcnRtZW50Lmdsb2JhbFRoaXNcbiAgICAgIH1cblxuICAgICAgLy8gc2F2ZSB0aGUgY29tcGFydG1lbnQgZm9yIHVzZSBieSBvdGhlciBtb2R1bGVzIGluIHRoZSBwYWNrYWdlXG4gICAgICBwYWNrYWdlQ29tcGFydG1lbnRDYWNoZS5zZXQocm9vdFBhY2thZ2VOYW1lLCByb290UGFja2FnZUNvbXBhcnRtZW50KVxuXG4gICAgICByZXR1cm4gcm9vdFBhY2thZ2VDb21wYXJ0bWVudFxuICAgIH1cblxuICAgIGZ1bmN0aW9uIGdldENvbXBhcnRtZW50Rm9yUGFja2FnZSAocGFja2FnZU5hbWUsIHBhY2thZ2VQb2xpY3kpIHtcbiAgICAgIC8vIGNvbXBhcnRtZW50IG1heSBoYXZlIGFscmVhZHkgYmVlbiBjcmVhdGVkXG4gICAgICBsZXQgcGFja2FnZUNvbXBhcnRtZW50ID0gcGFja2FnZUNvbXBhcnRtZW50Q2FjaGUuZ2V0KHBhY2thZ2VOYW1lKVxuICAgICAgaWYgKHBhY2thZ2VDb21wYXJ0bWVudCkge1xuICAgICAgICByZXR1cm4gcGFja2FnZUNvbXBhcnRtZW50XG4gICAgICB9XG5cbiAgICAgIC8vIHByZXBhcmUgQ29tcGFydG1lbnRcbiAgICAgIGlmIChnZXRFeHRlcm5hbENvbXBhcnRtZW50ICYmIHBhY2thZ2VQb2xpY3kuZW52KSB7XG4gICAgICAgIC8vIGV4dGVybmFsIGNvbXBhcnRtZW50IGNhbiBiZSBwcm92aWRlZCBieSB0aGUgcGxhdGZvcm0gKGVnIGxhdmFtb2F0LW5vZGUpXG4gICAgICAgIHBhY2thZ2VDb21wYXJ0bWVudCA9IGdldEV4dGVybmFsQ29tcGFydG1lbnQocGFja2FnZU5hbWUsIHBhY2thZ2VQb2xpY3kpXG4gICAgICB9IGVsc2Uge1xuICAgICAgICAvLyBwcmVwYXJlIHRoZSBtb2R1bGUncyBTRVMgQ29tcGFydG1lbnRcbiAgICAgICAgLy8gZW5kb3dtZW50czpcbiAgICAgICAgLy8gLSBNYXRoIGlzIGZvciB1bnRhbWVkIE1hdGgucmFuZG9tXG4gICAgICAgIC8vIC0gRGF0ZSBpcyBmb3IgdW50YW1lZCBEYXRlLm5vd1xuICAgICAgICBwYWNrYWdlQ29tcGFydG1lbnQgPSBuZXcgQ29tcGFydG1lbnQoeyBNYXRoLCBEYXRlIH0pXG4gICAgICB9XG4gICAgICAvLyBwcmVwYXJlIGVuZG93bWVudHNcbiAgICAgIGxldCBlbmRvd21lbnRzXG4gICAgICB0cnkge1xuICAgICAgICBlbmRvd21lbnRzID0gZ2V0RW5kb3dtZW50c0ZvckNvbmZpZyhcbiAgICAgICAgICAvLyBzb3VyY2UgcmVmZXJlbmNlXG4gICAgICAgICAgcm9vdFBhY2thZ2VDb21wYXJ0bWVudC5nbG9iYWxUaGlzLFxuICAgICAgICAgIC8vIHBvbGljeVxuICAgICAgICAgIHBhY2thZ2VQb2xpY3ksXG4gICAgICAgICAgLy8gdW53cmFwIHRvXG4gICAgICAgICAgZ2xvYmFsUmVmLFxuICAgICAgICAgIC8vIHVud3JhcCBmcm9tXG4gICAgICAgICAgcGFja2FnZUNvbXBhcnRtZW50Lmdsb2JhbFRoaXNcbiAgICAgICAgKVxuICAgICAgfSBjYXRjaCAoZXJyKSB7XG4gICAgICAgIGNvbnN0IGVyck1zZyA9IGBMYXZhbW9hdCAtIGZhaWxlZCB0byBwcmVwYXJlIGVuZG93bWVudHMgZm9yIHBhY2thZ2UgXCIke3BhY2thZ2VOYW1lfVwiOlxcbiR7ZXJyLnN0YWNrfWBcbiAgICAgICAgdGhyb3cgbmV3IEVycm9yKGVyck1zZylcbiAgICAgIH1cblxuICAgICAgLy8gdHJhbnNmb3JtIGZ1bmN0aW9ucywgZ2V0dGVycyAmIHNldHRlcnMgb24gcHJvcCBkZXNjcy4gU29sdmVzIFNFUyBzY29wZSBwcm94eSBidWdcbiAgICAgIE9iamVjdC5lbnRyaWVzKE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3JzKGVuZG93bWVudHMpKVxuICAgICAgICAvLyBpZ25vcmUgbm9uLWNvbmZpZ3VyYWJsZSBwcm9wZXJ0aWVzIGJlY2F1c2Ugd2UgYXJlIG1vZGlmeWluZyBlbmRvd21lbnRzIGluIHBsYWNlXG4gICAgICAgIC5maWx0ZXIoKFtrZXksIHByb3BEZXNjXSkgPT4gcHJvcERlc2MuY29uZmlndXJhYmxlKVxuICAgICAgICAuZm9yRWFjaCgoW2tleSwgcHJvcERlc2NdKSA9PiB7XG4gICAgICAgICAgY29uc3Qgd3JhcHBlZFByb3BEZXNjID0gYXBwbHlFbmRvd21lbnRQcm9wRGVzY1RyYW5zZm9ybXMocHJvcERlc2MsIHBhY2thZ2VDb21wYXJ0bWVudCwgcm9vdFBhY2thZ2VDb21wYXJ0bWVudC5nbG9iYWxUaGlzKVxuICAgICAgICAgIFJlZmxlY3QuZGVmaW5lUHJvcGVydHkoZW5kb3dtZW50cywga2V5LCB3cmFwcGVkUHJvcERlc2MpXG4gICAgICAgIH0pXG5cbiAgICAgIC8vIHNldHMgdXAgcmVhZC93cml0ZSBhY2Nlc3MgYXMgY29uZmlndXJlZFxuICAgICAgY29uc3QgZ2xvYmFsc0NvbmZpZyA9IHBhY2thZ2VQb2xpY3kuZ2xvYmFsc1xuICAgICAgcHJlcGFyZUNvbXBhcnRtZW50R2xvYmFsRnJvbUNvbmZpZyhwYWNrYWdlQ29tcGFydG1lbnQsIGdsb2JhbHNDb25maWcsIGVuZG93bWVudHMsIGdsb2JhbFN0b3JlLCBnbG9iYWxUaGlzUmVmcylcblxuICAgICAgLy8gc2F2ZSB0aGUgY29tcGFydG1lbnQgZm9yIHVzZSBieSBvdGhlciBtb2R1bGVzIGluIHRoZSBwYWNrYWdlXG4gICAgICBwYWNrYWdlQ29tcGFydG1lbnRDYWNoZS5zZXQocGFja2FnZU5hbWUsIHBhY2thZ2VDb21wYXJ0bWVudClcblxuICAgICAgcmV0dXJuIHBhY2thZ2VDb21wYXJ0bWVudFxuICAgIH1cblxuICAgIC8vIHRoaXMgZ2V0cyB0aGUgbGF2YU1vYXQgY29uZmlnIGZvciBhIG1vZHVsZSBieSBwYWNrYWdlTmFtZVxuICAgIC8vIGlmIHRoZXJlIHdlcmUgZ2xvYmFsIGRlZmF1bHRzIChlLmcuIGV2ZXJ5dGhpbmcgZ2V0cyBcImNvbnNvbGVcIikgdGhleSBjb3VsZCBiZSBhcHBsaWVkIGhlcmVcbiAgICBmdW5jdGlvbiBnZXRQb2xpY3lGb3JQYWNrYWdlIChjb25maWcsIHBhY2thZ2VOYW1lKSB7XG4gICAgICBjb25zdCBwYWNrYWdlQ29uZmlnID0gKGNvbmZpZy5yZXNvdXJjZXMgfHwge30pW3BhY2thZ2VOYW1lXSB8fCB7fVxuICAgICAgcGFja2FnZUNvbmZpZy5nbG9iYWxzID0gcGFja2FnZUNvbmZpZy5nbG9iYWxzIHx8IHt9XG4gICAgICBwYWNrYWdlQ29uZmlnLnBhY2thZ2VzID0gcGFja2FnZUNvbmZpZy5wYWNrYWdlcyB8fCB7fVxuICAgICAgcGFja2FnZUNvbmZpZy5idWlsdGluID0gcGFja2FnZUNvbmZpZy5idWlsdGluIHx8IHt9XG4gICAgICByZXR1cm4gcGFja2FnZUNvbmZpZ1xuICAgIH1cblxuICAgIC8vIHV0aWwgZm9yIGdldHRpbmcgdGhlIHByb3RvdHlwZSBjaGFpbiBhcyBhbiBhcnJheVxuICAgIC8vIGluY2x1ZGVzIHRoZSBwcm92aWRlZCB2YWx1ZSBpbiB0aGUgcmVzdWx0XG4gICAgZnVuY3Rpb24gZ2V0UHJvdG90eXBlQ2hhaW4gKHZhbHVlKSB7XG4gICAgICBjb25zdCBwcm90b0NoYWluID0gW11cbiAgICAgIGxldCBjdXJyZW50ID0gdmFsdWVcbiAgICAgIHdoaWxlIChjdXJyZW50ICYmICh0eXBlb2YgY3VycmVudCA9PT0gJ29iamVjdCcgfHwgdHlwZW9mIGN1cnJlbnQgPT09ICdmdW5jdGlvbicpKSB7XG4gICAgICAgIHByb3RvQ2hhaW4ucHVzaChjdXJyZW50KVxuICAgICAgICBjdXJyZW50ID0gUmVmbGVjdC5nZXRQcm90b3R5cGVPZihjdXJyZW50KVxuICAgICAgfVxuICAgICAgcmV0dXJuIHByb3RvQ2hhaW5cbiAgICB9XG4gIH1cbn0pKClcblxuICAgIGNvbnN0IGtlcm5lbCA9IGNyZWF0ZUtlcm5lbENvcmUoe1xuICAgICAgbGF2YW1vYXRDb25maWcsXG4gICAgICBsb2FkTW9kdWxlRGF0YSxcbiAgICAgIGdldFJlbGF0aXZlTW9kdWxlSWQsXG4gICAgICBwcmVwYXJlTW9kdWxlSW5pdGlhbGl6ZXJBcmdzLFxuICAgICAgZ2V0RXh0ZXJuYWxDb21wYXJ0bWVudCxcbiAgICAgIGdsb2JhbFJlZixcbiAgICAgIGdsb2JhbFRoaXNSZWZzLFxuICAgICAgZGVidWdNb2RlXG4gICAgfSlcbiAgICByZXR1cm4ga2VybmVsXG4gIH1cbn0pKClcblxuICBjb25zdCB7IGludGVybmFsUmVxdWlyZSB9ID0gY3JlYXRlS2VybmVsKHtcbiAgICBsYXZhbW9hdENvbmZpZyxcbiAgICBsb2FkTW9kdWxlRGF0YSxcbiAgICBnZXRSZWxhdGl2ZU1vZHVsZUlkLFxuICAgIHByZXBhcmVNb2R1bGVJbml0aWFsaXplckFyZ3MsXG4gICAgZ2xvYmFsVGhpc1JlZnM6IFsnd2luZG93JywgJ3NlbGYnLCAnZ2xvYmFsJywgJ2dsb2JhbFRoaXMnXVxuICB9KVxuXG4gIC8vIGNyZWF0ZSBhIGxhdmFtb2F0IHB1bGljIEFQSSBmb3IgbG9hZGluZyBtb2R1bGVzIG92ZXIgbXVsdGlwbGUgZmlsZXNcbiAgY29uc3QgbGF2YW1vYXRQdWJsaWNBcGkgPSBPYmplY3QuZnJlZXplKHtcbiAgICBsb2FkQnVuZGxlOiBPYmplY3QuZnJlZXplKGxvYWRCdW5kbGUpLFxuICB9KVxuICBnbG9iYWxSZWYuTGF2YU1vYXQgPSBsYXZhbW9hdFB1YmxpY0FwaVxuXG4gIHJldHVybiBsb2FkQnVuZGxlXG5cblxuICAvLyBpdCBpcyBjYWxsZWQgYnkgdGhlIG1vZHVsZXMgY29sbGVjdGlvbiB0aGF0IHdpbGwgYmUgYXBwZW5kZWQgdG8gdGhpcyBmaWxlXG4gIGZ1bmN0aW9uIGxvYWRCdW5kbGUgKG5ld01vZHVsZXMsIGVudHJ5UG9pbnRzLCBuZXdDb25maWcpIHtcbiAgICAvLyB2ZXJpZnkgKyBsb2FkIGNvbmZpZ1xuICAgIE9iamVjdC5lbnRyaWVzKG5ld0NvbmZpZy5yZXNvdXJjZXMgfHwge30pLmZvckVhY2goKFtwYWNrYWdlTmFtZSwgcGFja2FnZUNvbmZpZ10pID0+IHtcbiAgICAgIGlmIChwYWNrYWdlTmFtZSBpbiBsYXZhbW9hdENvbmZpZykge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoYExhdmFNb2F0IC0gbG9hZEJ1bmRsZSBlbmNvdW50ZXJlZCByZWR1bmRhbnQgY29uZmlnIGRlZmluaXRpb24gZm9yIHBhY2thZ2UgXCIke3BhY2thZ2VOYW1lfVwiYClcbiAgICAgIH1cbiAgICAgIGxhdmFtb2F0Q29uZmlnLnJlc291cmNlc1twYWNrYWdlTmFtZV0gPSBwYWNrYWdlQ29uZmlnXG4gICAgfSlcbiAgICAvLyB2ZXJpZnkgKyBsb2FkIGluIGVhY2ggbW9kdWxlXG4gICAgZm9yIChjb25zdCBbbW9kdWxlSWQsIG1vZHVsZURhdGFdIG9mIE9iamVjdC5lbnRyaWVzKG5ld01vZHVsZXMpKSB7XG4gICAgICAvLyB2ZXJpZnkgdGhhdCBtb2R1bGUgaXMgbmV3XG4gICAgICBpZiAobW9kdWxlSWQgaW4gbW9kdWxlcykge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoYExhdmFNb2F0IC0gbG9hZEJ1bmRsZSBlbmNvdW50ZXJlZCByZWR1bmRhbnQgbW9kdWxlIGRlZmluaXRpb24gZm9yIGlkIFwiJHttb2R1bGVJZH1cImApXG4gICAgICB9XG4gICAgICAvLyBhZGQgdGhlIG1vZHVsZVxuICAgICAgbW9kdWxlc1ttb2R1bGVJZF0gPSBtb2R1bGVEYXRhXG4gICAgfVxuICAgIC8vIHJ1biBlYWNoIG9mIGVudHJ5UG9pbnRzXG4gICAgY29uc3QgZW50cnlFeHBvcnRzID0gQXJyYXkucHJvdG90eXBlLm1hcC5jYWxsKGVudHJ5UG9pbnRzLCAoZW50cnlJZCkgPT4ge1xuICAgICAgcmV0dXJuIGludGVybmFsUmVxdWlyZShlbnRyeUlkKVxuICAgIH0pXG4gICAgLy8gd2VicGFjayBjb21wYXQ6IHJldHVybiB0aGUgZmlyc3QgbW9kdWxlJ3MgZXhwb3J0c1xuICAgIHJldHVybiBlbnRyeUV4cG9ydHNbMF1cbiAgfVxuXG4gIGZ1bmN0aW9uIGxvYWRNb2R1bGVEYXRhIChtb2R1bGVJZCkge1xuICAgIHJldHVybiBtb2R1bGVzW21vZHVsZUlkXVxuICB9XG5cbiAgZnVuY3Rpb24gZ2V0UmVsYXRpdmVNb2R1bGVJZCAocGFyZW50TW9kdWxlSWQsIHJlcXVlc3RlZE5hbWUpIHtcbiAgICBjb25zdCBwYXJlbnRNb2R1bGVEYXRhID0gbW9kdWxlc1twYXJlbnRNb2R1bGVJZF1cbiAgICBpZiAoIShyZXF1ZXN0ZWROYW1lIGluIHBhcmVudE1vZHVsZURhdGEuZGVwcykpIHtcbiAgICAgIGNvbnNvbGUud2FybihgbWlzc2luZyBkZXA6ICR7cGFyZW50TW9kdWxlRGF0YS5wYWNrYWdlfSByZXF1ZXN0ZWQgJHtyZXF1ZXN0ZWROYW1lfWApXG4gICAgfVxuICAgIHJldHVybiBwYXJlbnRNb2R1bGVEYXRhLmRlcHNbcmVxdWVzdGVkTmFtZV0gfHwgcmVxdWVzdGVkTmFtZVxuICB9XG5cbiAgZnVuY3Rpb24gcHJlcGFyZU1vZHVsZUluaXRpYWxpemVyQXJncyAocmVxdWlyZVJlbGF0aXZlV2l0aENvbnRleHQsIG1vZHVsZU9iaiwgbW9kdWxlRGF0YSkge1xuICAgIGNvbnN0IHJlcXVpcmUgPSByZXF1aXJlUmVsYXRpdmVXaXRoQ29udGV4dFxuICAgIGNvbnN0IG1vZHVsZSA9IG1vZHVsZU9ialxuICAgIGNvbnN0IGV4cG9ydHMgPSBtb2R1bGVPYmouZXhwb3J0c1xuXG4gICAgLy8gYnJvd3NlcmlmeSBnb29wOlxuICAgIC8vIHRoaXMgXCJtb2R1bGVzXCIgaW50ZXJmYWNlIGlzIGV4cG9zZWQgdG8gdGhlIGJyb3dzZXJpZnkgbW9kdWxlSW5pdGlhbGl6ZXJcbiAgICAvLyBodHRwczovL2dpdGh1Yi5jb20vYnJvd3NlcmlmeS9icm93c2VyLXBhY2svYmxvYi9jZDBiZDMxZjhjMTEwZTE5YTgwNDI5MDE5YjY0ZTg4N2IxYTgyYjJiL3ByZWx1ZGUuanMjTDM4XG4gICAgLy8gYnJvd3NlcmlmeSdzIGJyb3dzZXItcmVzb2x2ZSB1c2VzIFwiYXJndW1lbnRzWzRdXCIgdG8gZG8gZGlyZWN0IG1vZHVsZSBpbml0aWFsaXphdGlvbnNcbiAgICAvLyBicm93c2VyaWZ5IHNlZW1zIHRvIGRvIHRoaXMgd2hlbiBtb2R1bGUgcmVmZXJlbmNlcyBhcmUgcmVkaXJlY3RlZCBieSB0aGUgXCJicm93c2VyXCIgZmllbGRcbiAgICAvLyB0aGlzIHByb3h5IHNoaW1zIHRoaXMgYmVoYXZpb3JcbiAgICAvLyB0aGlzIGlzIHV0aWxpemVkIGJ5IGJyb3dzZXJpZnkncyBkZWR1cGUgZmVhdHVyZVxuICAgIC8vIHRob3VnaCBpbiB0aGUgb3JpZ2luYWwgYnJvd3Nlci1wYWNrIHByZWx1ZGUgaXQgaGFzIGEgc2lkZSBlZmZlY3QgdGhhdCBpdCBpcyByZS1pbnN0YW50aWF0ZWQgZnJvbSB0aGUgb3JpZ2luYWwgbW9kdWxlIChubyBzaGFyZWQgY2xvc3VyZSBzdGF0ZSlcbiAgICBjb25zdCBkaXJlY3RNb2R1bGVJbnN0YW50aWF0aW9uSW50ZXJmYWNlID0gbmV3IFByb3h5KHt9LCB7XG4gICAgICBnZXQgKF8sIHRhcmdldE1vZHVsZUlkKSB7XG4gICAgICAgIGNvbnN0IGZha2VNb2R1bGVEZWZpbml0aW9uID0gW2Zha2VNb2R1bGVJbml0aWFsaXplcl1cbiAgICAgICAgcmV0dXJuIGZha2VNb2R1bGVEZWZpbml0aW9uXG5cbiAgICAgICAgZnVuY3Rpb24gZmFrZU1vZHVsZUluaXRpYWxpemVyICgpIHtcbiAgICAgICAgICBjb25zdCB0YXJnZXRNb2R1bGVFeHBvcnRzID0gcmVxdWlyZVJlbGF0aXZlV2l0aENvbnRleHQodGFyZ2V0TW9kdWxlSWQpXG4gICAgICAgICAgbW9kdWxlT2JqLmV4cG9ydHMgPSB0YXJnZXRNb2R1bGVFeHBvcnRzXG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9KVxuXG4gICAgcmV0dXJuIFtyZXF1aXJlLCBtb2R1bGUsIGV4cG9ydHMsIG51bGwsIGRpcmVjdE1vZHVsZUluc3RhbnRpYXRpb25JbnRlcmZhY2VdXG4gIH1cblxufSkoKVxuIl19
