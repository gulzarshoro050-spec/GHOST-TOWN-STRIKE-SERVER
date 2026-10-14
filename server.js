
// Ghost Town Strike - local save server (no dependencies).  Run:  node server.js   then open http://localhost:3000
const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto');
const PORT=+process.env.PORT||3000,HOST=process.env.HOST||'127.0.0.1';   // HOST=0.0.0.0 exposes it to your network
const FILE=path.join(__dirname,'ghost_town_data.json'),GAME=path.join(__dirname,'Ghost_Town_Strike.html');
const DAY=23*36e5,TTL=30*864e5,NOW=()=>Date.now();
// ---------- storage: users map has no prototype, so a name like "__proto__" can never collide with built-ins
const D={users:Object.create(null)},IDX=new Map();   // IDX: sha256(session token) -> username
try{Object.assign(D.users,JSON.parse(fs.readFileSync(FILE,'utf8')).users)}catch(e){}
for(const n in D.users){const a=D.users[n];a.tk=(Array.isArray(a.tk)?a.tk:[]).filter(t=>t&&t.h&&t.e>NOW());a.tk.forEach(t=>IDX.set(t.h,n))}   // old plain-text sessions are dropped
let wr=0,dirty=0;const flush=()=>{if(wr){dirty=1;return}wr=1;fs.writeFile(FILE+'.tmp',JSON.stringify(D),{mode:0o600},e=>{if(e){wr=0;return}fs.rename(FILE+'.tmp',FILE,()=>{wr=0;if(dirty){dirty=0;flush()}})})};
// ---------- passwords: scrypt + random 16-byte salt per user; only salt, parameters and hash are stored, never the password
const SC={N:32768,r:8,p:1,len:64};
const kdf=(pw,salt,o)=>new Promise((res,rej)=>crypto.scrypt(pw,salt,o.len,{N:o.N,r:o.r,p:o.p,maxmem:128*o.N*o.r+8388608},(e,k)=>e?rej(e):res(k)));   // async: never blocks the server
const mkPw=async p=>{const s=crypto.randomBytes(16);return{s:s.toString('hex'),h:(await kdf(p.normalize('NFKC'),s,SC)).toString('hex'),...SC}};
const same=(a,b)=>a.length==b.length&&crypto.timingSafeEqual(a,b);
async function checkPw(a,p){const L=!a.pw,rec=L?{N:16384,r:8,p:1,len:32}:a.pw;   // L = account made by the first server version (upgraded on next login)
 const k=await kdf(L?p:p.normalize('NFKC'),L?Buffer.from(a.salt):Buffer.from(a.pw.s,'hex'),rec);return same(k,Buffer.from(L?a.hash:a.pw.h,'hex'))}
// ---------- sessions: random 256-bit token, only its SHA-256 is stored, 30-day expiry
const th=t=>crypto.createHash('sha256').update(t).digest('hex');
function issue(n){const a=D.users[n],t=crypto.randomBytes(32).toString('hex'),h=th(t);if(a.tk.length>=5)IDX.delete(a.tk.shift().h);a.tk.push({h,e:NOW()+TTL});IDX.set(h,n);return t}
function who(q){const m=/^Bearer ([0-9a-f]{64})$/.exec(q.headers.authorization||'');if(!m)return;const h=th(m[1]),n=IDX.get(h),a=n&&D.users[n],e=a&&a.tk.find(x=>x.h==h);if(e&&e.e>NOW())return n;IDX.delete(h)}
// ---------- rate limiting (in memory)
const RL=new Map(),limited=(k,max,win)=>{const n=NOW(),r=(RL.get(k)||[]).filter(t=>n-t<win);RL.set(k,r);return r.length>=max},hit=k=>RL.set(k,[...(RL.get(k)||[]),NOW()]);setInterval(()=>RL.clear(),36e5).unref();
// ---------- save validation: the server rebuilds every save field by field and never stores unknown keys
const PRICES={8:125,12:75,18:105,19:90},GOALS=[5,10,15,10,7],WODS=[4,17,8],STATS=['kills','hs','played','wins','sweeps','deaths'];
const ACH=[['kills',1],['hs',25],['kills',100],['played',10],['wins',3],['sweeps',1]];   // [stat, goal] per achievement
const bad=m=>{throw Object.assign(new Error(m),{bad:1})},stale=()=>{throw Object.assign(new Error('Save is older than the server copy'),{stale:1})};
const isInt=(v,a,b)=>Number.isInteger(v)&&v>=a&&v<=b,isObj=v=>v&&typeof v=='object'&&!Array.isArray(v);
const FRESH=()=>({cash:0,ts:0,tk:null,own:[],ac:{},st:{kills:0,hs:0,played:0,wins:0,sweeps:0,deaths:0}});
const spent=own=>(own||[]).reduce((s,i)=>s+(PRICES[i]||0),0);
function validate(s,prev,acct){   // returns a trusted, rebuilt save or throws
 if(!isObj(s))bad('Save must be an object');
 const now=NOW(),o=FRESH(),P=Object.assign(FRESH(),prev||{});P.st=Object.assign(FRESH().st,P.st);P.ac=P.ac||{};P.own=Array.isArray(P.own)?P.own:[];
 if(!isInt(s.cash,0,1e6))bad('Invalid cash');o.cash=s.cash;
 if(!isObj(s.st))bad('Invalid stats');
 for(const k of STATS){if(!isInt(s.st[k],0,1e6))bad('Invalid stat: '+k);if(s.st[k]<(+P.st[k]||0))stale();o.st[k]=s.st[k]}   // lifetime stats can never go down
 if(o.st.wins>o.st.played||o.st.sweeps>o.st.wins)bad('Inconsistent stats');
 if(!Array.isArray(s.own)||s.own.length>Object.keys(PRICES).length)bad('Invalid weapons');
 for(const i of s.own){if(!Number.isInteger(i)||!PRICES[i]||o.own.includes(i))bad('Invalid weapon');o.own.push(i)}
 if(!P.own.every(i=>o.own.includes(i)))stale();   // purchases can't be removed
 if(!isObj(s.ac))bad('Invalid achievements');
 ACH.forEach((a,i)=>{const v=s.ac[i]===undefined?0:s.ac[i];if(!isInt(v,0,2))bad('Invalid achievement');if(v&&o.st[a[0]]<a[1])bad('Achievement not earned');if(v<(+P.ac[i]||0))stale();if(v)o.ac[i]=v});
 const t=s.tk;if(t!==null){if(!isObj(t)||!isInt(t.at,0,now+DAY+36e5)||!WODS.includes(t.w)||!Array.isArray(t.p)||!Array.isArray(t.c)||t.p.length!=5||t.c.length!=5)bad('Invalid tasks');
  o.tk={at:t.at,w:t.w,p:[],c:[]};for(let i=0;i<5;i++){if(!isInt(t.p[i],0,GOALS[i])||(t.c[i]!==0&&t.c[i]!==1)||(t.c[i]&&t.p[i]<GOALS[i]))bad('Invalid task progress');o.tk.p.push(t.p[i]);o.tk.c.push(t.c[i])}}
 if(!isInt(s.ts,0,now+864e5))bad('Invalid timestamp');o.ts=s.ts;
 // plausibility: total cash ever earned (balance + weapons bought) can't exceed what matches, daily tasks and achievements can pay out
 const earned=o.cash+spent(o.own),max=acct?acct.base.earned+Math.max(0,o.st.played-acct.base.played)*90+145*(Math.floor((now-acct.created)/DAY)+1)+230:o.st.played*90+145*60+230;
 if(earned>max)bad('Progress failed validation');
 return o}
// ---------- http
const J=(r,c,o)=>{r.writeHead(c,{'Content-Type':'application/json','Cache-Control':'no-store','X-Content-Type-Options':'nosniff','Access-Control-Allow-Origin':'*','Access-Control-Allow-Headers':'Content-Type,Authorization','Access-Control-Allow-Methods':'GET,POST,PUT,OPTIONS'});r.end(JSON.stringify(o))};
const HE=(m,status)=>Object.assign(new Error(m),{status});
const body=q=>new Promise((res,rej)=>{let b='',n=0;q.on('data',c=>{n+=c.length;if(n>1e5){rej(HE('Request too large',413));q.destroy();return}b+=c});q.on('end',()=>{try{const j=JSON.parse(b||'{}');isObj(j)?res(j):rej(HE('Invalid JSON',400))}catch(e){rej(HE('Invalid JSON',400))}})});
http.createServer(async(q,r)=>{const u=q.url.split('?')[0],ip=q.socket.remoteAddress;
 if(q.method=='OPTIONS')return J(r,204,{});
 if(u=='/'||u=='/index.html')return fs.readFile(GAME,(e,d)=>{if(e){r.writeHead(404);return r.end('Put Ghost_Town_Strike.html next to server.js')}r.writeHead(200,{'Content-Type':'text/html; charset=utf-8','X-Content-Type-Options':'nosniff'});r.end(d)});
 if(!u.startsWith('/api/'))return J(r,404,{error:'Not found'});
 try{
  if(u=='/api/signup'&&q.method=='POST'){const b=await body(q),n=typeof b.username=='string'?b.username.toLowerCase():'';
   if(!/^[a-z][a-z0-9_]{2,15}$/.test(n))return J(r,400,{error:'Username: 3-16 characters, start with a letter, then letters, numbers or _'});
   if(typeof b.password!='string'||b.password.length<8||b.password.length>128)return J(r,400,{error:'Password must be 8-128 characters'});
   if(b.password.toLowerCase()==n)return J(r,400,{error:'Password must not match the username'});
   if(limited('S|'+ip,10,36e5))return J(r,429,{error:'Too many sign-ups. Try again later.'});
   if(Object.hasOwn(D.users,n))return J(r,409,{error:'Username already taken'});
   let save,note;try{save=validate(b.save===undefined?FRESH():b.save,null,null)}catch(e){if(!e.bad)throw e;save=FRESH();note='Your guest progress could not be verified, so the account started fresh. Guest progress is still on this device.'}
   const pw=await mkPw(b.password);if(Object.hasOwn(D.users,n))return J(r,409,{error:'Username already taken'});
   D.users[n]={pw,tk:[],save,created:NOW(),base:{earned:save.cash+spent(save.own),played:save.st.played}};hit('S|'+ip);const t=issue(n);flush();return J(r,200,{token:t,username:n,save,note})}
  if(u=='/api/login'&&q.method=='POST'){const b=await body(q),n=typeof b.username=='string'?b.username.toLowerCase().slice(0,32):'';
   if(typeof b.password!='string'||b.password.length>128)return J(r,400,{error:'Invalid request'});
   const k='L|'+ip+'|'+n;if(limited(k,5,9e5))return J(r,429,{error:'Too many failed attempts. Try again in 15 minutes.'});
   const a=Object.hasOwn(D.users,n)?D.users[n]:null,ok=a?await checkPw(a,b.password):(await mkPw(b.password),false);   // unknown names cost the same time as wrong passwords
   if(!ok){hit(k);return J(r,401,{error:'Wrong username or password'})}
   if(!a.pw){a.pw=await mkPw(b.password);delete a.salt;delete a.hash}   // upgrade old hashes
   const t=issue(n);flush();return J(r,200,{token:t,username:n,save:a.save})}
  const n=who(q);if(!n)return J(r,401,{error:'Unauthorized'});const a=D.users[n];
  if(u=='/api/save'&&q.method=='GET')return J(r,200,{save:a.save});
  if(u=='/api/save'&&q.method=='PUT'){const b=await body(q);
   if(!a.base)a.base={earned:(+a.save.cash||0)+spent(a.save.own),played:+(a.save.st&&a.save.st.played)||0};if(!a.created)a.created=NOW();   // accounts from the first version
   try{a.save=validate(b.save,a.save,a)}catch(e){if(e.bad)return J(r,400,{error:e.message});if(e.stale)return J(r,409,{error:e.message,save:a.save});throw e}
   flush();return J(r,200,{ok:1})}
  if(u=='/api/logout'&&q.method=='POST'){const h=th(q.headers.authorization.slice(7));a.tk=a.tk.filter(x=>x.h!=h);IDX.delete(h);flush();return J(r,200,{ok:1})}
  J(r,404,{error:'Not found'})
 }catch(e){J(r,e.status||500,{error:e.status?e.message:'Server error'})}
}).listen(PORT,HOST,()=>console.log(`Ghost Town Strike server: http://${HOST==='0.0.0.0'?'localhost':HOST}:${PORT}  (saves to ${FILE})`));
