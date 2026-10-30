//================ MATH UTILITIES
const clamp=(x,a,b)=>Math.min(Math.max(x,a),b)
const norm=(dx,dy)=>Math.sqrt(dx*dx + dy*dy)
const harmonicMean=(x,y)=>2*x*y/(x+y+1e-17)
function interp(x,y,X) {
    const n=x.length, Q=[...y];
    for(let i=1; i<n; ++i) for(let j=0; j<n-i; ++j) Q[j]=((X-x[j])*Q[j+1] - (X-x[j+i])*Q[j])/(x[j+i]-x[j])
    return Q[0]
}
// const rangauss=()=>Math.sqrt(-2.0*Math.log(1-Math.random())) * Math.cos(2.0*Math.PI*Math.random()) //Box-Muller
function rangauss() { // Marsaglia
    if(rangauss.y) {const x=rangauss.y;rangauss.y=null; return x}
    let u,v,s; do {u=Math.random()*2-1;v=Math.random()*2-1;s=u*u+v*v} while (s>= 1||s===0)
    let f=Math.sqrt(-2.*Math.log(s)/s); rangauss.y=f*v; return f*u
}
//================ GLOBAL SIMULATION VARIABLES
const ctx=canvas.getContext("2d")
var frameSkip,B,T,tPresent
//-------- PHYSICAL CONSTANTS AND UNITS
const pi   = 3.141592653589793238
const gam  = 0.577215664901532861
const kB   = 1.380649e-23
const hbar = 1.054571817e-34
const mu0  = 1.25663706127e-6
const M    = 2 * 9.1093837e-31  // Cooper pair mass
const Q    = 2 * 1.60217663e-19 // Cooper pair charge
const PhiQ = 2*pi*hbar/Q        // superconducting flux quantum in Wb
const nm   = 1e-9
const ps   = 1e-12
const Kelvin=1
const xUnit   = 1.e-9 // length unit (nanometer)
const EUnit   = kB*1.0 // energy unit (kB*K)
const tUnit = hbar/EUnit
const mUnit = EUnit*tUnit**2/xUnit**2
//-------- SIMULATION CONSTANTS
const X=160,Y=100,I=X*Y  // grid size
const a=10*nm            // grid spacing
const hThickness = 7*nm// 7nm
const tRelax = 1.00*ps
const tOsc   = 0.50*ps
const tStep  = 0.05*ps
const mFict  = 7.7e-72   // hardwire????????????  this depends on thckness....???!1
const zetaDamp=Math.exp(-tStep/tRelax)
const zetaKick=tRelax*(1-zetaDamp) / tUnit
//-------- SIMULATION ARRAYS
const xi0=new Float32Array(I),lam0=new Float32Array(I)
const Tc=new Float32Array(I)
const alpha=new Float32Array(I) // GL parameters
const beta=new Float32Array(I)
const w=new Float32Array(I)
const wx=new Float32Array(I),wy=new Float32Array(I)
const Ax=new Float32Array(I),Ay=new Float32Array(I)
const u=new Float32Array(I),v=new Float32Array(I)
const p=new Float32Array(I),q=new Float32Array(I)
//-------- OPTIONAL ARRAYS (e.g., VORTICITY, ENERGY, B FIELD)
const theta=new Float32Array(I),Omega=new Float32Array(I)
const Kx=new Float32Array(I),Ky=new Float32Array(I) // currents or dummies
let insulators = [];

//==== Structs for repetitive data types
class Vortex {
    constructor(x,y, value) {
        this.x = x;
        this.y = y;
        this.value = value;
    }
}

class Insulator {
    constructor(x0,x1,y0,y1) {
        this.vortices = [];
        this.x0 = x0;
        this.x1 = x1;
        this.y0 = y0;
        this.y1 = y1;
    }
}

//================ FUNCTIONS
function addRectangle(xUnit, y0, x1, y1, xi0_, lam0_, Tc_) {
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y
        if (xUnit<x && x<x1 && y0<y && y<y1) {xi0[i]=xi0_; lam0[i]=lam0_; Tc[i]=Tc_;}
    }

    // If xUnit === 0, or y0 === 0 we aren't in a valid insulator location
    if (xUnit > 0 && y0 > 0) {
        addInsulator(new Insulator(
            xUnit, x1, y0, y1
        ));
    }
}
function addEllipse(xc, yc, a, b, xi0_, lam0_, Tc_) {
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y
        if (((x-xc)/a)**2 + ((y-yc)/b)**2 < 1) {xi0[i]=xi0_; lam0[i]=lam0_; Tc[i]=Tc_;}
    }
}
function addInsulator(newInsulator) {
    if (!newInsulator instanceof Insulator) {
        return;
    }
    insulators.push(newInsulator);
}
function clearInsulators() {
    insulators = [];
}
function sumVorticesInInsulator(insulator) {
    if (!insulator instanceof Insulator) {
        return NaN;
    }
    let total = 0;
    insulator.vortices.forEach((element, index, array) => {
        total += element.value;
    })
    return total;
}
function isInsideInsulator(insulator,x,y) {
    if (!insulator instanceof Insulator) {
        return false;
    }
    return (x > insulator.x0 && y > insulator.y0 && x < insulator.x1 && y < insulator.y1);
}
function bcsGapEquation(ToverTc) {
    const xi=[0., 0.0954915, 0.345492, 0.654508, 0.904508, 1.]
    const yi=[1., 1., 0.98649, 0.754135, 0.265597, 0.]
    return interp(xi, yi, ToverTc)
}
function bcsSuperfluidStiffness(ToverTc) {
    const xi=[0., 0.0954915, 0.345492, 0.654508, 0.904508, 1.]
    const yi=[1, 1., 0.96241, 0.626009, 0.187307, 0]
    return interp(xi, yi, ToverTc)
}
function updatewxwy() {
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y
        const xp=(x+1)%X,iE=xp+X*y
        const yp=(y+1)%Y,iN=x+X*yp
        wx[i]=x<X-1? harmonicMean(w[i], w[iE]) : 0
        wy[i]=y<Y-1? harmonicMean(w[i], w[iN]) : 0
    }
}
function initWF() {
    tPresent = 0.
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y
        const psi0 = beta[i]==0 ? 0 : (Math.abs(alpha[i])/beta[i])**.5
        u[i]=(Math.random()-.5) * psi0   // u and v are in simulation units
        v[i]=(Math.random()-.5) * psi0
        p[i]=0.
        q[i]=0.
    }
}


function calcPars(xi0, lam0, Tc, T, h) { // convert material & simulation parameters to GL parameters in SI units
    let w,alpha,beta
    if (Tc<0) { // MATERIAL IS INSULATOR
        w    = 0
        alpha= (hbar**2)/(4*M*xi0**2) *3*(25/14.-1)* h  // HARDWIRE QUESTIONABLE FORMULA !!!!!!!!!!
        beta = mu0*Q**2*hbar**2*lam0**2/(4*M**2*xi0**2) * (0.5 + 25/14.) * h // QUESTIONABLE!!!
    }
    else if (T>=Tc) { // SUPERCONDUCTOR ABOVE ITS Tc
        w    = hbar**2/(2*M) * h        // warning: would overflow if single precision
        alpha= (hbar**2)/(4*M*xi0**2) * 3*(T/Tc-1) * h
        beta = mu0*Q**2*hbar**2*lam0**2/(4*M**2*xi0**2) * (0.5 + T/Tc) * h
    }
    else { // SUPERCONDUCTOR
        const xi =xi0/bcsGapEquation(T/Tc)
        const lam=lam0/bcsSuperfluidStiffness(T/Tc)**.5
        w    = hbar**2/(2*M)  * h
        alpha= -(hbar**2)/(4*M*xi**2) * h
        beta = mu0*Q**2*hbar**2*lam**2/(4*M**2*xi**2) * h
    }
    return [alpha,beta,w]
}
function setB(e) {
    B = Number(sliderB.value)*1e-3
    labelB.innerHTML = 'B = '+B/1e-3+'mT'
    const piaBOverPhiQ=pi*a*B/PhiQ, xcen=(X-1)/2, ycen=(Y-1)/2
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y
        Ax[i]=piaBOverPhiQ*(ycen-y)*a
        Ay[i]=piaBOverPhiQ*(x-xcen)*a
    }
}
function setT(e) {
    T = Number(sliderT.value)
    labelT.innerHTML = `TStat = ${T} K`
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y
        const [aaa,bbb,www] = calcPars(xi0[i], lam0[i], Tc[i], T, hThickness) // these are in SI units
        alpha[i]=aaa/(EUnit*xUnit)    * (a/xUnit)**2  // include these stepszie factors
        beta[i] =bbb/(EUnit*xUnit**4) * (a/xUnit)**2
        w[i]    =www/(EUnit*xUnit**3)
    }
    updatewxwy()
}
function setMisc(e) {
    frameSkip = Number(sliderframeskip.value)
    labelframeskip.innerHTML = `Frameskip = ${frameSkip}`
}
function evolve() {
    const zetaDiffuse = Math.sqrt(mFict*kB*T*(1-zetaDamp**2))   / (mUnit*xUnit**5*EUnit)**.5
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) { // calculate forces
        const xp=(x+1)%X,xm=(x+X-1)%X
        const yp=(y+1)%Y,ym=(y+Y-1)%Y
        const i=x+X*y,iE=xp+X*y,iW=xm+X*y,iN=x+X*yp,iS=x+X*ym
        let c,s,ui=u[i],vi=v[i]
        const Zi = -alpha[i] - beta[i]*(ui**2 + vi**2)/2
        // need to check sense
        c=Math.cos(Ax[i]) ;s= Math.sin(Ax[i]) ; const uE=c*u[iE] - s*v[iE] - ui, vE=s*u[iE] + c*v[iE] - vi
        c=Math.cos(Ax[iW]);s=-Math.sin(Ax[iW]); const uW=c*u[iW] - s*v[iW] - ui, vW=s*u[iW] + c*v[iW] - vi
        c=Math.cos(Ay[i]) ;s= Math.sin(Ay[i]) ; const uN=c*u[iN] - s*v[iN] - ui, vN=s*u[iN] + c*v[iN] - vi
        c=Math.cos(Ay[iS]);s=-Math.sin(Ay[iS]); const uS=c*u[iS] - s*v[iS] - ui, vS=s*u[iS] + c*v[iS] - vi
        const f = wx[i]*uE + wx[iW]*uW + wy[i]*uN + wy[iS]*uS + Zi*ui
        const g = wx[i]*vE + wx[iW]*vW + wy[i]*vN + wy[iS]*vS + Zi*vi
        // kick+damp+diffuse
        p[i] = zetaKick*f + zetaDamp*p[i] + zetaDiffuse*rangauss()
        q[i] = zetaKick*g + zetaDamp*q[i] + zetaDiffuse*rangauss()
    }
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y
        u[i] += p[i]*tStep/mFict     * (mUnit*xUnit**5)/tUnit
        v[i] += q[i]*tStep/mFict     * (mUnit*xUnit**5)/tUnit
    }
    tPresent += tStep
}

const rem=(x)=>(x - Math.round(x))
function findVorticity() {
    // Compute phases (theta), quasi-currents (Kx and Ky), and vorticity (Omega)
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y
        theta[i] = Math.atan2(v[i], u[i])
    }
    const ootwopi = 1/(2*3.14159265358979)
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {
        if (x<X-1) Kx[x+X*y] = rem(ootwopi*(theta[(x+1)+X*y] - theta[x+X*y] - Ax[x+X*y]))
        if (y<Y-1) Ky[x+X*y] = rem(ootwopi*(theta[x+X*(y+1)] - theta[x+X*y] - Ay[x+X*y]))
    }
    const mixingFactor = 0.5
    for (let x=0; x<X-1; ++x) for (let y=0; y<Y-1; ++y) {const i=x+X*y
        const xp = (x+1)%X
        const yp = (y+1)%Y
        const OmegaVal = Math.round(Kx[x+X*y] - Kx[x+X*yp] - Ky[x+X*y] + Ky[xp+X*y])
        // USE MIXING FACTOR TO GET TRAILS
        Omega[i] = (1-mixingFactor)*Omega[i] + mixingFactor * OmegaVal
    }
}

function hsv2rgb(h,s,v) { //h in [0,2*pi] and s,v in [0,1]; r,g,b in [0,255]
    const f= (n,k=(n+h*3/Math.PI)%6) => Math.floor(255*(v - v*s*Math.max( Math.min(k,4-k,1), 0)))
    return [f(5),f(3),f(1)]
}
function drawVortex(x,y) {
    ctx.beginPath()
    ctx.moveTo(x+.5,y+.5); ctx.lineTo(x+1.5,y+1.5)
    ctx.moveTo(x+1.5,y+.5); ctx.lineTo(x+.5,y+1.5)
    ctx.stroke()
}
function drawAntiVortex(x,y) {
    ctx.beginPath()
    ctx.ellipse(x+1,y+1, .5,.5, 0, 0,2*Math.PI)
    ctx.stroke()
}
function animate(timeCurrent) {
    ctx.clearRect(0, 0, canvas.width, canvas.height)
    for (let i=0; i<frameSkip; ++i) evolve()
    const pixScale = Math.min(Math.floor(canvas.width/X),Math.floor(canvas.height/Y))
    ctx.setTransform(pixScale, 0, 0, -pixScale, 0, canvas.height)
    const magTypical = 0.05
    //======== Wave function amplitude & phase heatmap
    if (cbWF.checked) { // if Wavefunction checkbox is checked, draw
        for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y
            const arg=Math.atan2(v[i],u[i])
            const mag=(u[i]**2+v[i]**2) / magTypical
            const [r,g,b] = hsv2rgb(arg, 1, mag/(1+mag))
            ctx.fillStyle= `rgb(${r}, ${g}, ${b})`
            ctx.fillRect(x,y,1,1)
        }
    }
    //======== Vorticity
    if (cbVort.checked) {
        findVorticity();
        insulators.forEach( (element, index, array) => {
            element.vortices = [];
        });
        ctx.lineWidth=.4; ctx.strokeStyle='#FFFFFF'
        for (let x=1; x<X-1; ++x) for (let y=1; y<Y-1; ++y) {const i=x+X*y
            if (Tc[i]<0) {
                ctx.globalAlpha = 1.
                ctx.fillStyle='#666666'  // gray moat
                ctx.fillRect(x,y,1,1)

                insulators.forEach( (element, index, array) => {

                    if (isInsideInsulator(element,x,y)) {
                        if (Omega[i] > 0) element.vortices.push(new Vortex(x,y,1))
                        else if (Omega[i] < 0) element.vortices.push(new Vortex(x,y,-1))
                    }
                })


                continue   // do not draw vortex inside an insulator



                /**
                 * PLAN: Create a vortex counter which is contained within an insulator class
                 *       Maybe keep an exact count of each through a specific JSON object format,
                 *             which keeps the location and value of each vortex and has a counting function on the prototype
                 *             Then update the list in this loop, and after loop, draw the numbers
                 *
                 */
            }

            ctx.globalAlpha = Math.min(1, Math.abs(2.12*Omega[i]))
            if (Omega[i] > 0)      drawVortex(x,y)
            else if (Omega[i] < 0) drawAntiVortex(x,y)



            // ctx.globalAlpha = Math.abs(10*Omega[i])
            // ctx.fillStyle = Omega[i]>0 ? '#FFFF99': '#99FFFF'
            // ctx.fillRect(x,y,1,1)
        }
        ctx.globalAlpha = 1.
    }
    const scaleBarLen=50*nm,scaleBarText='50 nm'
    const X1=X-8-scaleBarLen/a, X2=X-8, Y1=Y-8, Y2=Y-8
    const insuPt = ctx.getTransform().transformPoint({x:X1,y:Y2})
    ctx.beginPath();ctx.moveTo(X1,Y1); ctx.lineTo(X2,Y2); ctx.strokeStyle='#FFFFFF'; ctx.stroke()
    const pt = ctx.getTransform().transformPoint({x:X1,y:Y2})
    ctx.resetTransform();

    ctx.font = 'italic bold 48px sans-serif';
    ctx.fillStyle = 'white';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';

    insulators.forEach( (element, index, array) => {
        let sum = sumVorticesInInsulator(element).toString();

        let x = ((element.x1 - element.x0) / 2) + element.x0;
        let y = ((element.y1 - element.y0) / 2) + element.y0;

        ctx.fillText(sum, x * pixScale, (y + 5) * pixScale);
    })


    //======== Scale bar
    // const scaleBarLen=50*nm,scaleBarText='50 nm'
    // const X1=X-8-scaleBarLen/a, X2=X-8, Y1=Y-8, Y2=Y-8
    // ctx.beginPath();ctx.moveTo(X1,Y1); ctx.lineTo(X2,Y2); ctx.strokeStyle='#FFFFFF'; ctx.stroke()
    // const pt = ctx.getTransform().transformPoint({x:X1,y:Y2})
    ctx.resetTransform()
    ctx.font = '12px Arial'; ctx.textBaseline = "bottom"; ctx.fillStyle='#FFF'
    ctx.fillText(scaleBarText, pt.x, pt.y-4)
    //======== Thermometer based on KE
    let TMeter = 0
    for (let x=0; x<X; ++x) for (let y=0; y<Y; ++y) {const i=x+X*y; TMeter+=p[i]**2+q[i]**2}
    TMeter *= 1/(2*X*Y*kB*mFict) * EUnit**2*tUnit**2*xUnit**3
    sliderTMeter.value = TMeter
    labelTMeter.innerHTML = `TMeter= ${TMeter.toFixed(2)} K`
    //======== Report properties of simulation cell at crosshair
    reportCellProperties()
    requestAnimationFrame(animate)
}
function resize() {
    canvas.width=visualViewport.width||window.innerWidth||document.documentElement.clientWidth||document.body.clientWidth
    canvas.height=visualViewport.height||window.innerHeight||document.documentElement.clientHeight||document.body.clientHeight
}
//================ MAIN CODE
document.body.addEventListener('dblclick', function (e) { e.preventDefault() })
window.visualViewport.addEventListener('resize', resize)
sliderB.addEventListener('input', setB)
sliderT.addEventListener('input', setT)
sliderframeskip.addEventListener('input', setMisc)


button1.addEventListener('click', (e)=>{
    clearInsulators();
    // addRectangle(-1, -1, X, Y,       4*nm, 400*nm, -14*Kelvin)  // insulating substrate by default!
    addRectangle(-1, -1,  X, Y,       4*nm, 400*nm, +14*Kelvin)  // NbTiN everywhere
    setB(); setT(); initWF(); setMisc(); resize();}
)
button2.addEventListener('click', (e)=>{
    clearInsulators();
    addRectangle(-1, -1, X, Y,             4*nm, 400*nm, -14*Kelvin)  // insulating substrate by default!
    addRectangle(.1*X, .1*Y, .2*X, .9*Y, 4*nm, 400*nm, +14*Kelvin)  // moat
    addRectangle(.3*X, .1*Y, .5*X, .9*Y, 4*nm, 400*nm, +14*Kelvin)  // moat
    addRectangle(.6*X, .1*Y, .9*X, .9*Y, 4*nm, 400*nm, +14*Kelvin)  // moat
    setB(); setT(); initWF(); setMisc(); resize();}
)
button3.addEventListener('click', (e)=>{
    clearInsulators();
    addRectangle(-1, -1, X, Y,             4*nm, 400*nm, -14*Kelvin)  // insulating substrate by default!
    addEllipse  (.2*X,.25*Y, .20*Y, .20*Y, 4*nm, 400*nm, +14*Kelvin) // NbTiN disk
    addEllipse  (.2*X,.25*Y, .18*Y, .18*Y, 4*nm, 400*nm, -14*Kelvin) // make into annulus
    addEllipse  (.2*X, .7*Y, .20*Y, .20*Y, 4*nm, 400*nm, +14*Kelvin) // NbTiN disk
    addEllipse  (.2*X, .7*Y, .15*Y, .15*Y, 4*nm, 400*nm, -14*Kelvin) // make into annulus
    addEllipse  (.5*X, .5*Y, .20*Y, .20*Y, 4*nm, 400*nm, +14*Kelvin) // NbTiN disk
    addEllipse  (.5*X, .5*Y, .12*Y, .12*Y, 4*nm, 400*nm, -14*Kelvin) // make into annulus
    addEllipse  (.8*X,.25*Y, .20*Y, .20*Y, 4*nm, 400*nm, +14*Kelvin) // NbTiN disk
    addEllipse  (.8*X,.25*Y, .06*Y, .06*Y, 4*nm, 400*nm, -14*Kelvin) // make into annulus
    addEllipse  (.8*X, .7*Y, .20*Y, .20*Y, 4*nm, 400*nm, +14*Kelvin) // NbTiN disk
    addEllipse  (.8*X, .7*Y, .02*Y, .02*Y, 4*nm, 400*nm, -14*Kelvin) // make into annulus
    setB(); setT(); initWF(); setMisc(); resize();}
)
button4.addEventListener('click', (e)=>{
    clearInsulators();
    addRectangle(-1, -1, X, Y,             4*nm, 400*nm, -14*Kelvin)  // insulating substrate by default!
    addRectangle(0, 0,   X, Y,         4*nm, 400*nm, +14*Kelvin)  // NbTiN everywhere
    const moatSpacing=.25*X     // center-to-center spacing
    const a=.08*X               // moat side
    for (let i=-2; i<=2; i+=2) {
        for (let j=-1; j<=1; j+=2) {
            const x1=.5*X+i*moatSpacing/2, y1=.5*Y+j*moatSpacing/2, side=.1*X
            addRectangle(x1-a/2, y1-a/2, x1+a/2, y1+a/2, 4*nm, 400*nm, -14*Kelvin)  // moat
        }
    }
    setB(); setT(); initWF(); setMisc(); resize();}
)
button5.addEventListener('click', (e)=>{
    clearInsulators();
    addRectangle(-1, -1, X, Y,             4*nm, 400*nm, -14*Kelvin)  // insulating substrate by default!
    const x1=.31*X,x2=.69*X,b=.30*Y,a=.26*Y
    addEllipse  (x1, .5*Y, b, b, 4*nm, 400*nm, +14*Kelvin) // NbTiN disk
    addEllipse  (x1, .5*Y, a, a, 4*nm, 400*nm, -14*Kelvin) // make into annulus
    addEllipse  (x2, .5*Y, b, b, 4*nm, 400*nm, +14*Kelvin) // NbTiN disk
    addEllipse  (x2, .5*Y, a, a, 4*nm, 400*nm, -14*Kelvin) // make into annulus
    addEllipse  (x2+b, .5*Y, .02*X, .03*Y, 4*nm, 400*nm, -14*Kelvin) // notch
    setB(); setT(); initWF(); setMisc(); resize();}
)


let mouseX=-1,mouseY=-1;
function recordMousePosition(e) {
    // if (!(e.buttons&1)) return
    // e.preventDefault(); e.stopPropagation()
    const rect=canvas.getBoundingClientRect()
    mouseX=e.clientX-rect.left; mouseY=e.clientY-rect.top
}
function reportCellProperties() {
    const pixScale = Math.min(Math.floor(canvas.width/X),Math.floor(canvas.height/Y)) // blah, redo this
    ctx.setTransform(pixScale, 0, 0, -pixScale, 0, canvas.height)
    const pt=ctx.getTransform().invertSelf().transformPoint({x:mouseX,y:mouseY})
    const x=Math.floor(pt.x),y=Math.floor(pt.y)
    if (x<0||x>=X||y<0||y>=Y) {
        statusDiv.innerHTML = 'Move crosshair to examine'
        return
    }
    const i=x+X*y
    statusDiv.innerHTML =
        `Tc=${Tc[i]}  xi0=${(xi0[i]/nm).toFixed(0)}nm  lam0=${(lam0[i]/nm).toFixed(0)}nm  `+
        `|&psi;|=${Math.sqrt(u[i]**2+v[i]**2).toFixed(3)}  t=${(tPresent/ps).toFixed(2)}ps`
    // `(x,y)=(${x},${y})   alpha=${alpha[i].toFixed(0)}   beta=${beta[i].toFixed(0)}   w=${w[i].toFixed(0)}

}
// canvas.addEventListener('mousedown', reportCellProperties)
canvas.addEventListener('mousemove', recordMousePosition)

// initMatter(); setB(); setT(); initWF(); setMisc(); resize();
button1.click(); requestAnimationFrame(animate);