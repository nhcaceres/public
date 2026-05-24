using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using System.Runtime.InteropServices;
using System.IO;

namespace Hamilton
{
    class BetaGenerator
    {
        #region Variables
        const int maxCantLlaves = 200;
        
        int[] v = new int[maxCantLlaves];           // valores booleanos
        int[] wIdx = new int[maxCantLlaves];        // Indices foraneos
        int[] w = new int[maxCantLlaves];           // valores booleanos foraneos en orden de SEE
        int wLastIdx;                               // ultimo indice asignado
        char[] wChar = new char[maxCantLlaves];     // valores foraneos en orden de SEE. Formato cadena de caracteres
        int[] wVal = new int[maxCantLlaves];        // Valor "asociado" a la variable
        int[] staticValue= new int[maxCantLlaves];  // valores estaticos
        int _totalLaves;
        int _llavesCerradas;
        int _llavesAbiertas;
        Index[] I = new Index[maxCantLlaves];      // contadores por niveles de anidamiento
        char[] vchar = new char[maxCantLlaves];   // valores en codificación ascii
        int numBytes;                             // cantidad de bytes para almacenar los bits binarios
        byte[] vBits = new byte[maxCantLlaves];     // valores en codificación binaria   * Revisar p/ cada experimento * en c++ era unsigned char
        int lastStaticIndex;
       
        bool cutModeON;
  
        int cantLlavesBLQ;

        int unosFijos;
        int cerosFijos;

        int iCut;
        int fCut;
        int nCut;
        int cut_unos;       // Unos en el area de corte
        int cut_ceros;      // Ceros en el area de corte

        int banderaFin;

        bool ultimoLeido = false; // indica que se leyo el ult reg del STORAGE. La proxima vez será eof

        System.IO.FileStream fs = null;
        System.IO.BinaryWriter sw = null;
        System.IO.BinaryReader sr = null;
        #endregion

        public int TotalLlaves
        {
            get { return _totalLaves; }
        }

        public int LlavesCerradas
        {
            get { return _llavesCerradas; }
        }

        public int LlavesAbiertas
        {
            get { return _llavesAbiertas; }
        }
     
        #region ----- Constructores -------------
        public BetaGenerator() {
            for (int i = 0; i < maxCantLlaves; i++)
            {
                I[i] = new Index();
            }
            _totalLaves = 0;
            lastStaticIndex = -1;
            unosFijos = 0;
            cerosFijos = 0;
            iCut = 0;
            fCut = 0;
            cutModeON = false;
            wLastIdx = 0;

            nCut = 0;           // ancho del area de corte
            cut_unos = 0;       // Unos en el area de corte
            cut_ceros = 0;      // Ceros en el area de corte
            cantLlavesBLQ = 0;
            banderaFin = -1;
         
        }

        public BetaGenerator(int totalLlaves, int llavesCerradas) {
            for (int i = 0; i < maxCantLlaves; i++)
            {
                I[i] = new Index();
            }
            _totalLaves = 0;
            unosFijos = 0;
            cerosFijos = 0;
            iCut = 0;
            fCut = 0;
            cutModeON = false;
            wLastIdx = 0;
            SetDimention(totalLlaves, llavesCerradas);
            cantLlavesBLQ = 0;
        }
        #endregion 
        // ----- Destructor -------------
        //~BetaGenerator() { }

        #region SetDimention()
        public void SetDimention(int totalLlaves, int llavesCerradas)
        {
            SetDimention(totalLlaves, llavesCerradas, false);
        }

        void SetDimention(int totalLlaves, int llavesCerradas, bool cutModeValue)
        {
            cutModeON = cutModeValue;
            _totalLaves = totalLlaves;
            _llavesCerradas = llavesCerradas;
            _llavesAbiertas = _totalLaves - _llavesCerradas;
            inicializar();
        }
        #endregion  SetDimention()

        #region Inicializar
        public void inicializar()
        {
            if (_totalLaves > maxCantLlaves) throw new Exception("Maxima cantidad de llaves excedida");
            banderaFin = -1;

            #region  Asignar finales
            int u = _totalLaves - 1;
            int v = _llavesCerradas - 1;
            for (int i = 0; i < _llavesCerradas; i++)
            {
                I[v].ult = u;
                v--;
                u--;
            }
            #endregion Asignar finales

            #region  Asignar iniciales estáticos
            int unoIdx = 0;
            int iIdx = 0;
            for (int i = 0; i <= lastStaticIndex; i++)
            {
                if (staticValue[i] != 0)
                {
                    I[iIdx].ini = unoIdx;
                    I[iIdx].act = unoIdx;
                    I[iIdx].ult = unoIdx;
                    unoIdx++;
                    iIdx++;
                }
                else {
                    unoIdx++;
                }
            }
            #endregion  Asignar iniciales estáticos

            #region  Asignar iniciales  No-estaticos
            for (int i = iIdx; i < _llavesCerradas; i++)
            {
                I[iIdx].ini = unoIdx;
                I[iIdx].act = unoIdx;
                iIdx++;
                unoIdx++;
            }
            #endregion Asignar iniciales  No-estaticos

            numBytes = _totalLaves / (sizeof(byte) * 8);
            if (_totalLaves % (sizeof(byte) * 8) != 0) numBytes++;

            Generate(); // Ya genera la primera combinacion
            if (_llavesCerradas == 0 || _llavesAbiertas == 0) this.banderaFin = 0;
        }
        #endregion

        #region combinacionesBetaRadiales
        public static BigInteger CombinacionesBetaRadiales(int cerradas, int abiertas)
        {

            BigInteger fact_N = factorial(cerradas + abiertas);
            BigInteger fact_c = factorial(cerradas);
            BigInteger fact_a = factorial(abiertas);
            BigInteger comb = fact_N / fact_c / fact_a;
            if (comb == 0) comb = 1;
            return comb;
        }
        static BigInteger factorial(BigInteger numero)
        {
            BigInteger fact_N = 0;
            fact_N = numero;
            for (BigInteger i = numero - 1; i >= 1; i--)
            {
                fact_N = fact_N * i;
            }
            return fact_N;
        }
        #endregion combinacionesBetaRadiales

        #region Generate()
        public bool Generate()
        {
            int k;  // indice de nivel
            if (EndOfSequence()) return false;
            if (banderaFin == 0) banderaFin++;

            //----- Cerar unos ---
            for (k = 0; k < _totalLaves; k++)
            {
                v[k] = 0;
            }
            //----- Asigna unos ---
            for (int j = 0; j < _llavesCerradas; j++)
            {
                int idx = I[j].act;
                if (idx > I[j].ult)
                {
                    banderaFin = 1;
                    return !EndOfSequence();
                }         
                v[idx] = 1;
            }

            // incrementa el último nivel  -- El valor resultante se "usara" en el sigte Generate()
            int zi = unosFijos;
            k = _llavesCerradas - 1;

            I[k].act++;
            int ultimoModif = -1;
            // incrementa los niveles superiores si corresponde
            while (I[k].act > I[k].ult && k > 0)
            {   // Excedio limite y no es el nivel top=0
                ultimoModif = k;
                k--;
                I[k].act++;
                if (k == zi)
                {   // si se actualiza el último "modificable"
                    if (I[k].act > I[k].ult)
                    {
                        banderaFin = 0;
                    }
                }
            }

            // Inicializa los niveles inferiores desde el nivel que se modifico
            if (ultimoModif > -1)
            {
                for (int j = ultimoModif; j < _llavesCerradas; j++)
                {
                    I[j].act = I[j - 1].act + 1;
                }
            }
            return !EndOfSequence();
        }
        #endregion

        #region EndOfSequence()
        public bool EndOfSequence()
        {
            return (banderaFin > 0);
        }
        #endregion EndOfSequence()

        #region  InitializeSequence()
        public void InitializeSequence()
        {
            inicializar();
            // validacion
            if (_llavesCerradas - unosFijos < 2)
            {
                throw new Exception("--- El algoritmo requiere de por lo menos 2 unos móviles --- ");
            }
            if (lastStaticIndex >= 1)
            {
                if (unosFijos < 1)
                {
                    throw new Exception("--- Si hay valores fijos, por lo menos uno de ellos debe ser 'uno' --- ");
                }
            }
        }
        #endregion InitializeSequence()

        #region  GetCharacterArray() 
        public string GetCharacterArray()
        {
            string bf = "";
            int i;
            for (i = 0; i < _totalLaves; i++)
            {
                if( v[i] != 0)
                {
                    bf += "1";
                }
                else
                {
                    bf += "0";
                }
            }
            return bf;
        }
        #endregion  GetCharacterArray() 

        #region GetByteArray()
        //-------------------- GetByteArray() ----------------------
        // Replica la informacion contenida en el array de enteros v[] en el
        // array vBits[] que contiene la información en binario
        public byte[] GetByteArray()
        {
            int iB = numBytes - 1;
            int ib = 0;
            for (int i = 0; i < numBytes; i++)
            {
                vBits[i] = 0;
            }
            for (int i = _totalLaves - 1; i >= 0; i--)
            {
                if (v[i] != 0)
                {
                    vBits[iB] |= (byte)(1U << ib);
                }
                if (++ib > 7)
                {
                    iB--;
                    ib = 0;
                }
            }
            return vBits;
  }
        #endregion GetByteArray()

        #region GetValuesFromByteArray
        void GetValuesFromByteArray()
        {
            int iv = _totalLaves - 1;
            for (int i = _totalLaves - 1; i >= 0; i--)
            {
                v[i] = 0;
            }
            for (int iB = numBytes - 1; iB >= 0 && iv >= 0; iB--)
            {
                for (int ib = 0; ib < 8; ib++)
                {
                    if (iv >= 0)
                    {
                        int u = vBits[iB] & (1 << ib);
                        if ( u !=  0 )
                        {
                            v[iv] = 1;
                        }
                        else {
                            v[iv] = 0;
                        }
                    }
                    iv--;
                }
            }
        }
        #endregion GetValuesFromByteArray

        #region CreateStorage
        public void CreateStorage(string archivo, int total_llaves, int llaves_cerradas )
        {
            fs = new FileStream(archivo,FileMode.Create);
            sw = new BinaryWriter(fs);


            byte[] bytes = new byte[2];
            bytes[0] = (byte)(total_llaves >> 8);
            bytes[1] = (byte)total_llaves;
            sw.Write(bytes,0,2);

            bytes[0] = (byte)(llaves_cerradas >> 8);
            bytes[1] = (byte)llaves_cerradas;
            sw.Write(bytes, 0, 2);

        }
        #endregion CreateStorage

        #region CloseStorage
        public void CloseStorage()
        {
            if (sw != null) sw.Close();
            if (sr != null) sr.Close();
            if (fs != null) fs.Close();
        }
        #endregion CloseStorage()

        #region writeStorage
        public void writeStorage()
        {
            int len = sizeof(byte) * numBytes;
            GetByteArray(); // Copia la info al array vBits[]
            sw.Write(vBits,0, len);
        }
        #endregion writeStorage

        #region writeStorage (byte[] )
        public void writeStorage(byte[] arrayDeBits)
        {
            int len = sizeof(byte) * numBytes;
            sw.Write(arrayDeBits, 0, len);
        }
        #endregion writeStorage

        #region OpenStorage
        public void OpenStorage(string archivo)
        {
            ultimoLeido = false;
            if (System.IO.File.Exists(archivo))
            {
                CloseStorage();
                fs = new FileStream(archivo, FileMode.Open);
                sr = new BinaryReader(fs);

                byte[] bytes = new byte[2];

                sr.Read(bytes, 0, 2);
                int total_llaves = bytes[0];
                total_llaves = total_llaves << 8;
                total_llaves = total_llaves | bytes[1];

                sr.Read(bytes, 0, 2);
                int llaves_cerradas = bytes[0];
                llaves_cerradas = llaves_cerradas << 8;
                llaves_cerradas = llaves_cerradas | bytes[1];

                this.SetDimention(total_llaves, llaves_cerradas);
                ReadFromStorage(); // Leer el primer registro
            }
            else
            {
                throw new Exception( "El archivo STORAGE: "+ archivo+" No existe");
            }
        }
        #endregion OpenStorage

        #region ReadFromStorage
        public void ReadFromStorage()
        {
            try {
                int len = sizeof(byte) * numBytes;
                sr.Read(vBits, 0, len);
                GetValuesFromByteArray();
            }catch(Exception ex)
            {
                string mensaje = ex.Message;
            }
        }
        #endregion ReadFromStorage

        #region EndOfStorage
        public bool EndOfStorage()
        {
            bool ret = false;
            if (ultimoLeido || fs == null)
            {
                ret = true;
            }
            else
            {
                if (fs.Position >= fs.Length)
                {
                    ultimoLeido = true;
                }
            }
            return ret;
        }
        #endregion EndOfStorage

        #region ClearForeignPosition
        public void ClearForeignPosition()
        {
            wLastIdx = 0;
        }
        #endregion ClearForeignPosition

        #region ClearStaticPositions
        public void ClearStaticPositions()
        {
            lastStaticIndex = -1;
            unosFijos = 0;
            cerosFijos = 0;
            wLastIdx = 0;
        }
        #endregion ClearStaticPositions

        #region AddForeignPosition
        public int AddForeignPosition(int foreignPos)
        {
            int indiceAsignado = wLastIdx;
            wIdx[indiceAsignado] = foreignPos;
            wLastIdx++;
            return indiceAsignado;
        }
        #endregion AddForeignPosition

        #region AddForeignPosition
        public int AddForeignPosition(int foreignPos, int val)
        {
            int indiceAsignado = wLastIdx;
            wIdx[indiceAsignado] = foreignPos;
            wVal[indiceAsignado] = val;
            wLastIdx++;
            return indiceAsignado;
        }
        #endregion AddForeignPosition

        #region ForeignIndex
        public int ForeignIndex(int index)
        {
            return wIdx[index];
        }
        #endregion ForeignIndex

        #region ForeignVal
        public int ForeignVal(int index)
        {
            return wVal[index];
        }
        #endregion ForeignVal

        #region ForeignPositionsCounter
        public int ForeignPositionsCounter()
        {
            return wLastIdx;
        }
        #endregion ForeignPositionsCounter

        #region StaticPositionsCounter
        public int StaticPositionsCounter()
        {
            return (lastStaticIndex + 1);
        }
        #endregion StaticPositionsCounter

        #region ForeignArray
        public int[] ForeignArray()
        {
            for (int i = 0; i < _totalLaves; i++)
            {
                w[wIdx[i]] = v[i];
            }
            return w;
        }
        #endregion ForeignArray

        #region foreignCharString
        public string foreignCharString()
        {
            string buffer = new string(foreignCharArray());
            return buffer.Substring(0, _totalLaves);
        }
        #endregion foreignCharString

        #region foreignCharArray
        public char[] foreignCharArray()
        {
            int cantEstaticos = StaticPositionsCounter();
            for (int i = 0; i < _totalLaves; i++)
            {
                int wId = wIdx[i];
                if (v[i] != 0)
                {
                    wChar[wId] = '1';
                }
                else {
                    wChar[wId] = '0';
                }

                // sobrepone el valor estático  si corresponde
                if (i < cantEstaticos)
                {
                    if (staticValue[i] != 0)
                    {
                        wChar[wIdx[i]] = '1';
                    }
                    else {
                        wChar[wIdx[i]] = '0';
                    }
                }
            }
            return wChar;
        }
        #endregion foreignCharArray

        #region AddStaticValue
        public void AddStaticValue(int LogicIndex, int valor)
        {
            lastStaticIndex++;
            staticValue[lastStaticIndex] = valor;
            AddForeignPosition(LogicIndex, valor);
            if (valor != 0)
            {
                unosFijos++;
            }
            else {
                cerosFijos++;
            }
        }
        #endregion AddStaticValue

        #region SetCutRangeLen
        void SetCutRangeLen(int len)
        {
            nCut = len;
            if (lastStaticIndex < 0)
            {
                iCut = 0;
            }
            else {
                iCut = lastStaticIndex + 1;
            }
            fCut = iCut + len - 1;
        } // end setCutRangeLen
        #endregion SetCutRangeLen

        public int GetLastStaticIndex() { return lastStaticIndex; }
        public int GetUnosFijos() { return unosFijos; }
        public int GetCerosFijos() { return cerosFijos; }

    }// end class BetaGenerator --------------------------

    class Index
    {
        public int ini;
        public int ult;
        public int act;
    };

}// end namespace
