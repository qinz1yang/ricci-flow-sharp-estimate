from pathlib import Path
import sys,subprocess,fcntl,json,hashlib,datetime,os
p=Path(sys.argv[1]).resolve(); mod=sys.argv[2]; R=Path('/home/ubuntu/projects/rfse'); out=Path(__file__).parent/'imports';dst=out/(mod.replace('.','/')+'.lean');dst.parent.mkdir(parents=True,exist_ok=True)
if dst.is_symlink(): dst.unlink()
if dst.with_suffix('.olean').is_symlink(): dst.with_suffix('.olean').unlink()
dst.write_bytes(p.read_bytes())
opts=['-DautoImplicit=false','-Dpp.unicode.fun=true','-DmaxSynthPendingDepth=3','-Dweak.linter.mathlibStandardSet=true','-Dlinter.style.header.license=No license is granted by this file.']
with open(R/'.lake/rfse-root-writer.lock','a') as lock:
 fcntl.flock(lock,fcntl.LOCK_EX)
 lean=subprocess.check_output(['lake','env','which','lean'],cwd=R,text=True).strip(); lp=subprocess.check_output(['lake','env','printenv','LEAN_PATH'],cwd=R,text=True).strip()
 env=os.environ.copy();env['LEAN_PATH']=str(out)+':'+lp
 cmd=[lean,*opts,'--root='+str(out),'-o',str(dst.with_suffix('.olean')),str(dst)]
 r=subprocess.run(cmd,cwd=R,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
raw=Path(__file__).parent/(mod.split('.')[-1]+'.txt');raw.write_text(r.stdout);sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
raw.with_suffix('.completion.json').write_text(json.dumps({'command':cmd,'LEAN_PATH':env['LEAN_PATH'],'exit_code':r.returncode,'source_sha256':sha(dst),'output_sha256':sha(raw),'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()},indent=2)+'\n')
print(r.stdout);print('exit',r.returncode,flush=True);sys.exit(r.returncode)
